using SQLite
using SQLite.Tables
using SQLite.DBInterface: execute
using DataFrames
include(joinpath(@__DIR__, "FLS.jl"))

"""Data to specify a SQLite table"""
struct Tab
  name::String
  attrs::Vector{Tuple{String, String, Bool}}
  fks::Vector{Union{Pair{String,String},String}}
end

"""SQL create table statement"""
function add_tab(t::Tab, db::SQLite.DB)
  attrs = ["$k $v NOT NULL " * (u ? "UNIQUE" : "") for (k, v, u) in t.attrs]
  fks = [let (key, tgt) = k isa String ? ("$(k)_id", k) : k;
          ("$key INTEGER NOT NULL",
           "FOREIGN KEY ($key) REFERENCES $tgt ($(tgt)_id)") end
       for k in t.fks]
  fk1, fk2 = isempty(fks) ? ([],[]) : map(collect, zip(fks...)) # all attr decs, then all constraints
  parentunique = t.name == "PARENT" ? ["UNIQUE (parent, child)"] : []
  stmt = """CREATE TABLE IF NOT EXISTS $(t.name)
    \t($(t.name)_id INTEGER PRIMARY KEY AUTOINCREMENT,
    \t$(join(vcat(attrs,fk1, fk2, parentunique), ",\n\t")))"""
  SQLite.Stmt(db, stmt) |> execute
end
# Note: julia sqlite interface doesn't like BOOLEAN
tabs = [Tab("FLS", [("hash", "INTEGER", true),
                    ("name", "TEXT", true),
                    ("jdump","TEXT", true)], []),
    Tab("Premodel", [("hash", "INTEGER", true),
                     ("jdump", "TEXT", true),
                     ("size", "INTEGER", false),
                     ("fired", "INTEGER", false)], ["FLS"]), # ought be boolean
    Tab("Model", [("hash", "INTEGER", true),
                  ("jdump", "TEXT", true)], ["Premodel"]),
    Tab("Init", [("cards", "TEXT", true)], ["Premodel"]),
    Tab("Parent", [], ["parent"=>"Premodel", "child" => "Premodel"])]

function init_db(pth::Union{String,Nothing}=nothing;
                 rem::Bool=false)::SQLite.DB
  if rem
    rm(pth; force=true)
  end
  file = pth === nothing ? joinpath(@__DIR__, "../fls.db") : pth
  db = SQLite.DB(file)
  for t in tabs add_tab(t, db) end
  return db
end


"""
Given initial cardinalities for every nonlimit object, log the premodel they
correspond to.
"""
function init_premodel(db::SQLite.DB, F::FLS, cards::Vector{Int})::Int
  syms = sort(collect(realobs(F)))
  length(syms) == length(cards) || error("bad length: cards $cards syms $syms")
  d = Dict(zip(syms, cards))
  dstr = string(sort(collect(d)))
  i = add_premodel(db, F, initrel(F, d))
  execute(db, "INSERT INTO Init (cards, Premodel_id) VALUES (?,?)", [dstr,i])
  return i
end

"""Add FLS (if not already in DB) and return id"""
function add_fls(db::SQLite.DB, F::FLS)::Int
  ghash = canonical_hash(to_graph(F.schema))
  # check if already in db
  r = SQLite.getvalue(execute(db, "SELECT FLS_id FROM FLS WHERE hash=?",[ghash]), 1, Int)
  if r isa Int
    return r
  end

  execute(db, "INSERT INTO FLS (hash, name, jdump) VALUES (?,?,?)", [ghash,F.name,to_json(F)])
  z = execute(db, "SELECT last_insert_rowid()")
  return SQLite.getvalue(z,1,Int)
end

"""Get FLS by primary key id"""
function get_fls(db::SQLite.DB, i::Int)::FLS
  z = execute(db, "SELECT jdump FROM FLS WHERE FLS_id=?",[i])
  return fls_from_json(SQLite.getvalue(z,1,String))
end

"""Add premodel (if it doesn't exist) """
function add_premodel(db::SQLite.DB, F::FLS, m::StructACSet,
                      parent::Union{Int, Nothing}=nothing,
                      chash::Union{UInt64, Nothing}=nothing)::Int
  chash = chash === nothing ? canonical_hash(m) : chash
  # check if already in db
  r = SQLite.getvalue(execute(db,
    "SELECT Premodel_id FROM Premodel WHERE hash=?",[chash]), 1, Int)
  if !(r isa Int)
    fid = add_fls(db, F)
    execute(db, """INSERT INTO Premodel (hash, jdump, FLS_id, fired, size)
                    VALUES (?,?,?, false, ?)""",
            [chash,generate_json_acset(m),fid, relsize(F, m)])
    z = execute(db, "SELECT last_insert_rowid()")
    r = SQLite.getvalue(z,1,Int)
  end
  # Add parents if any
  if parent isa Int
    execute(db, "INSERT OR IGNORE INTO Parent(parent, child) VALUES(?, ?)",
            [parent,r])
  end
  return r
end

"""Add a premodel that is a model (if not already there). Return id"""
function add_model(db::SQLite.DB, F::FLS, relm::StructACSet,
                   parent::Union{Int, Nothing}=nothing,
                   relm_hsh::Union{UInt64, Nothing}=nothing)::Int
  m = crel_to_cset(F, relm) # fail if nonfunctional
  chash = canonical_hash(m)
  pid = add_premodel(db, F, relm, parent, relm_hsh)
  # check if already in db
  r = SQLite.getvalue(execute(db, "SELECT Model_id FROM Model WHERE hash=?",
                              [chash]), 1, Int)
  if r isa Int
    return r
  end

  execute(db, "INSERT INTO Model (hash, jdump, Premodel_id) VALUES (?,?,?)",
          [chash,generate_json_acset(m),pid])
  z = execute(db, "SELECT last_insert_rowid()")
  return SQLite.getvalue(z,1,Int)
end

"""Get premodel by primary key ID"""
function get_premodel(db::SQLite.DB, i::Int)::Pair{FLS, StructACSet}
  z = execute(db, "SELECT FLS.jdump AS f, Premodel.jdump as p FROM Premodel JOIN FLS USING (FLS_id) WHERE Premodel_id=?",[i])
  fls = fls_from_json(SQLite.getvalue(z,1,String))
  crel_type = typeof(grph_to_crel(fls.name, fls.schema))
  crel = parse_json_acset(crel_type,SQLite.getvalue(z,2,String))
  return fls => crel
end

"""All premodel hashes for an FLS"""
function get_seen(db::SQLite.DB, fls::FLS)::Set{UInt64}
  fid = add_fls(db, fls)
  z = execute(db, "SELECT hash FROM Premodel WHERE FLS_id=?",[fid]) |> DataFrame
  return Set(z[!,:hash])
end