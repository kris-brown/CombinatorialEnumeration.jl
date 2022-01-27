using Catlab
using CSetAutomorphisms
using LibPQ, Tables

include(joinpath(@__DIR__, "Sketch.jl"))

conn = LibPQ.Connection("dbname=models")
result = execute(conn, "SELECT typname FROM pg_type WHERE oid = 16")
data = columntable(result)

const FK_ = Union{Pair{String,String},String}
const Attr_ = Tuple{String, String, Bool}

"""Data to specify a table"""
struct Tab
  name::String
  attrs::Vector{Attr_}
  fks::Vector{FK_}
  uni::Vector{String}
end

Tab(n::String, at::Vector{Attr_}, fks::Vector{FK_})::Tab =
  Tab(n, at, fks, String[])

"""
SQL create table statement.
Hardcoded that the only nullable column is `Premodel.failed`
"""
function add_tab(t::Tab, conn::LibPQ.Connection)
  attrs = ["$k $v " * (k=="failed" ? "" : "NOT NULL ") * (u ? "UNIQUE" : "")
           for (k, v, u) in t.attrs]
  fks = [let (key, tgt) = k isa String ? ("$(k)_id", k) : k;
          ("$key INTEGER NOT NULL",
           "FOREIGN KEY ($key) REFERENCES $tgt ($(tgt)_id)") end
       for k in t.fks]
  # all attr decs, then all constraints
  fk1, fk2 = isempty(fks) ? ([],[]) : map(collect, zip(fks...))
  ustr = isempty(t.uni) ? "" : ", UNIQUE ($(join(t.uni,",")))"

  stmt = """CREATE TABLE IF NOT EXISTS $(t.name)
    \t($(t.name)_id SERIAL PRIMARY KEY,
    \t$(join(vcat(attrs,fk1, fk2), ",\n\t")) $ustr)"""
  execute(conn, stmt)
end

tabs = [Tab("Sketch", [("hash", "DECIMAL(20,0)", true),
                       ("name", "TEXT", true),
                       ("jdump","TEXT", true)], FK_[]),
    Tab("Premodel", [("hash", "DECIMAL(20,0)", true),
                     ("jdump", "TEXT", true),
                     ("failed", "BOOLEAN", false),
                     ("size", "INTEGER", false),], FK_["Sketch"]),
    Tab("Model", [("hash", "DECIMAL(20,0)", true),
                  ("jdump", "TEXT", true)], FK_["Premodel"]),
    Tab("Choice", [("delta", "TEXT", false)], FK_[ "parent"=>"Premodel",
      "child" => "Premodel"], ["delta", "parent", "child"]),
    Tab("Fired", Attr_[], FK_["parent"=>"Premodel", "child" => "Premodel"],
      ["parent", "child"])
      ]

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

function set_failed(db::LibPQ.Connection, pid::Int, f::Bool)::Nothing
  execute(db, "UPDATE Premodel SET failed = \$2 WHERE Premodel_id=\$1",
          [pid, f])
  return nothing
end
"""Add Sketch (if not already in DB) and return id"""
function add_sketch(db::LibPQ.Connection, F::Sketch)::Int
  ghash = hash(F)
  # check if already in db
  r = columntable(execute(db, "SELECT Sketch_id FROM Sketch WHERE hash=\$1",
                          [ghash]))
  if !(isempty(r[:sketch_id]))
    return r[:sketch_id][1]
  end

  z = columntable(execute(db,
    "INSERT INTO Sketch (hash, name, jdump) VALUES (\$1,\$2,\$3) " *
    "RETURNING Sketch_id", [ghash,F.name,to_json(F)]))[:sketch_id][1]
  return z
end

"""Get Sketch by primary key id"""
function get_sketch(db::LibPQ.Connection, i::Int)::Sketch
  msg = "SELECT jdump FROM Sketch WHERE Sketch_id=\$1"
  z = columntable(execute(db, msg,[i]))
  return sketch_from_json(z[:jdump][1])
end

"""Add the result of a `chase_step_db` step"""
function add_branch(db::LibPQ.Connection, S::Sketch, choice::String,
                   chased_premodel_id::Int, chosen_premodel::StructACSet)::Int
  new_id = add_premodel(db, S, chosen_premodel)
  msg = "INSERT INTO Choice(parent, child, delta) VALUES(\$1, \$2, \$3)"
  execute(db, msg * " ON CONFLICT DO NOTHING",
          [chased_premodel_id, new_id, string(choice)])
  return new_id
end

"""Add premodel (if it doesn't exist) """
function add_premodel(db::LibPQ.Connection, F::Sketch, m::StructACSet;
                      parent::Union{Int, Nothing}=nothing,
                      chash::Union{UInt64, Nothing}=nothing)::Int
  # println("\t adding premodel $m")
  chash = isnothing(chash) ? canonical_hash(m; pres=F.crel_pres) : chash
  # check if already in db
  r_ = columntable(execute(db,
    "SELECT Premodel_id FROM Premodel WHERE hash=\$1",[chash]))[:premodel_id]
  if isempty(r_)
    fid = add_sketch(db, F)
    jsn = generate_json_acset(m)
    r, = columntable(execute(db,
      """INSERT INTO Premodel (hash, jdump, Sketch_id, size)
         VALUES (\$1,\$2, \$3, \$4) RETURNING Premodel_id""",
            [chash, jsn, fid, relsize(F, m)]))[:premodel_id]
  else
    r, = r_
  end

  if parent isa Int # Add parents if any
    msg = "INSERT INTO Fired(parent, child) VALUES(\$1, \$2)"
    execute(db, msg * " ON CONFLICT DO NOTHING", [parent, r])
  end
  return r
end

"""Add a premodel that is a model (if not already there). Return id"""
function add_model(db::LibPQ.Connection, F::Sketch, relm::StructACSet,
                   parent::Int;
                   relm_hsh::Union{UInt64, Nothing}=nothing)::Int
  m, partial = crel_to_cset(F, relm) # fail if nonfunctional
  !partial || error("adding a partial model")
  pid = add_premodel(db, F, relm; parent=parent, chash=relm_hsh)

  # check if already in db
  chash = canonical_hash(m; pres=F.cset_pres)
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

"""Get premodel id if it exists from the premodel itself (which is hashed)"""
function get_premodel_id(db::LibPQ.Connection, crel::StructACSet,
                         crel_pres::Presentation)::Union{Nothing, Int}
  z = columntable(execute(db, """SELECT Premodel_id FROM Premodel
      WHERE hash=\$1""",[canonical_hash(crel, crel_pres)]))[:premodel_id]
  return (isempty(z) ? nothing : z[1])
end


"""Get premodel (as a cset, not crel) by primary key ID"""
function get_premodel(db::LibPQ.Connection, i::Int)::Pair{Sketch, StructACSet}
  z = columntable(execute(db, """SELECT Sketch.jdump AS f, Premodel.jdump as p
    FROM Premodel JOIN Sketch USING (Sketch_id) WHERE Premodel_id=\$1""",[i]))
  sketch = sketch_from_json(z[:f][1])
  modl = parse_json_acset(sketch.crel, z[:p][1])
  return sketch => crel_to_cset(sketch, modl)[1]
end

"""Get Model by primary key ID"""
function get_model(db::LibPQ.Connection, i::Int)::Pair{Sketch, StructACSet}
  z = columntable(execute(db, """SELECT Sketch.jdump AS f, Model.jdump as p
    FROM Model JOIN Premodel USING (Premodel_id)
               JOIN Sketch USING (Sketch_id) WHERE Model_id=\$1""", [i]))
  sketch = sketch_from_json(String(z[:f][1]))
  cset = parse_json_acset(sketch.cset, z[:p][1])
  return sketch => cset
end

get_models(db::LibPQ.Connection, S::Sketch, maxsize::Int)::Vector{StructACSet} =
  [get_model(db, i)[2] for i in get_model_ids(db,S,maxsize)]

function get_model_ids(db::LibPQ.Connection, S::Sketch, maxsize::Int
                      )::Vector{Int}
  q = """SELECT Model.model_id FROM Premodel
         JOIN Model USING (Premodel_id) JOIN Sketch USING (Sketch_id)
         WHERE name='$(S.name)' AND size <= $maxsize ORDER BY size"""
  return Int.(columntable(execute(db, q))[:model_id])
end

"""All premodel hashes for an Sketch that have been chased"""
function get_seen(db::LibPQ.Connection, sketch::Sketch, fired::Bool=false;
                  maxsize::Int=0)::Set{UInt64}
  fid = add_sketch(db, sketch)
  wc1 = maxsize == 0 ? "" : " AND size < $maxsize"
  wc2 = fired ? " AND fired" : ""
  msg = "SELECT hash FROM Premodel WHERE Sketch_id=\$1"*wc1*wc2
  z = columntable(execute(db, msg, [fid]))
  return Set(map(UInt64, z[:hash]))
end

function get_premodel_ids(db::LibPQ.Connection, sketch::Sketch;
                          unchased::Bool=false, maxsize::Int=0)::Vector{Int}
  fid = add_sketch(db, sketch)
  wc1 = maxsize == 0 ? "" : " AND size <= $maxsize"
  wc2 = unchased ? """ AND failed IS NULL""" : ""
  msg = "SELECT Premodel_id FROM Premodel WHERE Sketch_id=\$1"*wc1*wc2
  z = columntable(execute(db, msg * " ORDER BY size", [fid]))
  return collect(z[:premodel_id])
end


function get_premodels(db::LibPQ.Connection, sketch::Sketch; maxsize::Int=0
                      )::Vector{StructACSet}
  [get_premodel(db, Int64(i))[2] for i
   in get_premodel_ids(db, sketch; maxsize=maxsize)]
end
