using Catlab
using LibPQ, Tables

include(joinpath(@__DIR__, "FLS.jl"))

conn = LibPQ.Connection("dbname=models")
result = execute(conn, "SELECT typname FROM pg_type WHERE oid = 16")
data = columntable(result)

"""Data to specify a table"""
struct Tab
  name::String
  attrs::Vector{Tuple{String, String, Bool}}
  fks::Vector{Union{Pair{String,String},String}}
end

"""SQL create table statement"""
function add_tab(t::Tab, conn::LibPQ.Connection)::Nothing
  attrs = ["$k $v NOT NULL " * (u ? "UNIQUE" : "") for (k, v, u) in t.attrs]
  fks = [let (key, tgt) = k isa String ? ("$(k)_id", k) : k;
          ("$key INTEGER NOT NULL",
           "FOREIGN KEY ($key) REFERENCES $tgt ($(tgt)_id)") end
       for k in t.fks]
  fk1, fk2 = isempty(fks) ? ([],[]) : map(collect, zip(fks...)) # all attr decs, then all constraints
  parentunique = t.name == "PARENT" ? ["UNIQUE (parent, child)"] : []
  stmt = """CREATE TABLE IF NOT EXISTS $(t.name)
    \t($(t.name)_id SERIAL PRIMARY KEY,
    \t$(join(vcat(attrs,fk1, fk2, parentunique), ",\n\t")))"""
  execute(conn, stmt)
  return nothing
end

tabs = [Tab("FLS", [("hash", "DECIMAL(20,0)", true),
                    ("name", "TEXT", true),
                    ("jdump","TEXT", true)], []),
    Tab("Premodel", [("hash", "DECIMAL(20,0)", true),
                     ("jdump", "TEXT", true),
                     ("size", "INTEGER", false),
                     ("fired", "BOOLEAN", false)], ["FLS"]), # ought be boolean
    Tab("Model", [("hash", "DECIMAL(20,0)", true),
                  ("jdump", "TEXT", true)], ["Premodel"]),
    Tab("Init", [("cards", "TEXT", true)], ["Premodel"]),
    Tab("Parent", [("delta", "TEXT", false)], ["parent"=>"Premodel", "child" => "Premodel"])]

function init_db(; reset::Bool=false)::LibPQ.Connection
  conn = LibPQ.Connection("dbname=models")

  if reset
    for t in reverse(tabs)
      execute(conn, "DROP TABLE IF EXISTS $(t.name)")
    end
    for t in tabs
      add_tab(t, conn)
    end
  end
  return conn
end


"""
Given initial cardinalities for every nonlimit object, log the premodel they
correspond to.
"""
function init_premodel(db::LibPQ.Connection, F::FLS, cards::Vector{Int})::Int
  syms = sort(collect(realobs(F)))
  length(syms) == length(cards) || error("bad length: cards $cards syms $syms")
  d = Dict(zip(syms, cards))
  dstr = string(sort(collect(d)))
  r = columntable(execute(db, "SELECT Premodel_id FROM Init WHERE cards=\$1",
                              [dstr]))
  if !isempty(r[:premodel_id])
    return r[:premodel_id][1]
  end

  i = add_premodel(db, F, initrel(F, d))
  execute(db, "INSERT INTO Init (cards, Premodel_id) VALUES (\$1,\$2)", [dstr,i])
  return i
end

"""Add FLS (if not already in DB) and return id"""
function add_fls(db::LibPQ.Connection, F::FLS)::Int
  ghash = canonical_hash(to_graph(F.schema))
  # check if already in db
  r = columntable(execute(db, "SELECT FLS_id FROM FLS WHERE hash=\$1",[ghash]))
  if !(isempty(r[:fls_id]))
    return r[:fls_id][1]
  end

  z = columntable(execute(db,
    "INSERT INTO FLS (hash, name, jdump) VALUES (\$1,\$2,\$3) RETURNING FLS_id",
    [ghash,F.name,to_json(F)]))[:fls_id][1]
  return z
end

"""Get FLS by primary key id"""
function get_fls(db::LibPQ.Connection, i::Int)::FLS
  z = columntable(execute(db, "SELECT jdump FROM FLS WHERE FLS_id=\$1",[i]))
  return fls_from_json(z[:jdump][1])
end

"""Add premodel (if it doesn't exist) """
function add_premodel(db::LibPQ.Connection, F::FLS, m::StructACSet,
                      parent::Union{Int, Nothing}=nothing,
                      csd::Union{ChaseStepData, Nothing}=nothing,
                      chash::Union{UInt64, Nothing}=nothing)::Int
  chash = chash === nothing ? canonical_hash(m) : chash
  # check if already in db
  r = columntable(execute(db,
    "SELECT Premodel_id FROM Premodel WHERE hash=\$1",[chash]))[:premodel_id]
  if isempty(r)
    fid = add_fls(db, F)
    r = columntable(execute(db,
      """INSERT INTO Premodel (hash, jdump, FLS_id, fired, size)
         VALUES (\$1,\$2, \$3, false, \$4) RETURNING Premodel_id""",
            [chash,generate_json_acset(m), fid, relsize(F, m)]))[:premodel_id]
  end

  if parent isa Int # Add parents if any
    x =  columntable(execute(db,
      "SELECT Parent_id FROM Parent WHERE parent=\$1 AND child=\$2",
      [parent, r[1]]))[:parent_id]
    if isempty(x)
      execute(db, "INSERT INTO Parent(parent, child, delta) VALUES(\$1, \$2, \$3)", [parent, r[1], JSON.json(csd_to_dict(csd))])
    end
  end
  return r[1]
end

"""Add a premodel that is a model (if not already there). Return id"""
function add_model(db::LibPQ.Connection, F::FLS, relm::StructACSet,
                   parent::Union{Int, Nothing}=nothing,
                   csd::Union{ChaseStepData, Nothing}=nothing,
                   relm_hsh::Union{UInt64, Nothing}=nothing)::Int
  m, partial = crel_to_cset(F, relm) # fail if nonfunctional
  !partial || error("adding a partial model")
  chash = canonical_hash(m)
  pid = add_premodel(db, F, relm, parent, csd, relm_hsh)
  # check if already in db
  r = columntable(execute(db, "SELECT Model_id FROM Model WHERE hash=\$1",
                              [chash]))[:model_id]
  if !(isempty(r))
    return r[1]
  end

  z = columntable(execute(db, """INSERT INTO Model (hash, jdump, Premodel_id)
                                 VALUES (\$1,\$2,\$3) RETURNING Model_id""",
                          [chash, generate_json_acset(m), pid]))[:model_id]
  return z[1]
end

function get_premodel_id(db::LibPQ.Connection, crel::StructACSet)::Union{Nothing, Int}
  z = columntable(execute(db, """SELECT Premodel_id FROM Premodel
      WHERE hash=\$1""",[canonical_hash(crel)]))[:premodel_id]
  return (isempty(z) ? nothing : z[1])
end


"""Get premodel by primary key ID"""
function get_premodel(db::LibPQ.Connection, i::Int)::Pair{FLS, StructACSet}
  z = columntable(execute(db, """SELECT FLS.jdump AS f, Premodel.jdump as p
    FROM Premodel JOIN FLS USING (FLS_id) WHERE Premodel_id=\$1""",[i]))
  fls = fls_from_json(z[:f][1])
  crel = parse_json_acset(fls.crel, z[:p][1])
  return fls => crel
end

"""Get Model by primary key ID"""
function get_model(db::LibPQ.Connection, i::Int)::Pair{FLS, StructACSet}
  z = columntable(execute(db, """SELECT FLS.jdump AS f, Model.jdump as p
    FROM Model JOIN Premodel USING (Premodel_id)
               JOIN FLS USING (FLS_id) WHERE Model_id=\$1""",[i]))
  fls = fls_from_json(z[:f][1])
  cset = parse_json_acset(fls.cset, z[:p][1])
  return fls => cset
end

"""All premodel hashes for an FLS that have been chased"""
function get_seen(db::LibPQ.Connection, fls::FLS)::Set{UInt64}
  fid = add_fls(db, fls)
  z = columntable(execute(db,
    "SELECT hash FROM Premodel WHERE fired AND FLS_id=\$1",[fid]))
  return Set(map(UInt64, z[:hash]))
end