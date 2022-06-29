module DB
export init_db, get_premodel_ids, get_premodel, get_premodels, add_model,
       add_premodel, get_model, get_models, get_model_ids, set_failed,
       add_branch, EnumState, DBLike,  Db, start_premodel, set_fired

"""Interact with a postgres database"""

using ..Sketches
using ..Models

using Catlab.CategoricalAlgebra, Catlab.Present
using CSetAutomorphisms
using LibPQ, Tables, DataStructures

function nauty(x)
  for i in 1:5
    try
      h = call_nauty(x)
      return h
    catch _
      print("f $i ")
    end
  end
  error(generate_json_acset(x))
end

abstract type DBLike end
struct Db <: DBLike
  conn::LibPQ.Connection
end
# DB alternative: local memory
mutable struct EnumState <: DBLike
  premodels::Dict{UInt64, Pair{StructACSet, Defined}}
  pk::Vector{UInt64}
  models::Set{Int}
  sizes::Vector{Int}
  failed::Set{Int}
  fired::Dict{Int, Int}
  branch::DefaultDict{Int, Vector{Pair{Int, String}}}
  function EnumState()
    return new(
      Dict{UInt64, Pair{StructACSet, Defined}}(),UInt64[],
      Set{Int}(),Int[], Set{Int}(),Dict{Int, Int}(),
      DefaultDict{Int, Vector{Pair{Int, String}}}(
        ()->Pair{Int, String}[]))
  end
end

Base.length(es::EnumState) = length(es.premodels)
Base.getindex(es::EnumState, i::Int) = es.premodels[es.pk[i]]

function add_premodel(es::EnumState, S::Sketch, J::StructACSet, d::Defined;
                      parent::Union{Int, Nothing}=nothing,
                      chash::Union{UInt64, Nothing}=nothing)::Int
  chash = isnothing(chash) ? hash(nauty(J)) : chash
  if !isnothing(parent)
    es.fired[parent] = length(es.pk)
  end

  if haskey(es.premodels, chash)

    return findfirst(==(chash), es.pk)
  end
  push!(es.pk, chash)
  push!(es.sizes, relsize(S, J))
  es.premodels[chash] = J => d
  return length(es.pk)
end

function get_premodel_id(es::EnumState, crel::StructACSet,
  crel_pres::Presentation)::Union{Nothing, Int}
  hsh = hash(nauty(crel))
  return findfirst(==(hsh), es.pk)
end

function set_fired(es::EnumState, m::Int)
  es.fired[m] = m
end

function get_model_ids(es::EnumState, S::Sketch; maxsize::Int=0)::Vector{Int}
    is = [i for (i, s) in enumerate(es.sizes) if maxsize == 0 || s < maxsize]
    return collect(is ∩ es.models)
end

function get_model(es::EnumState, S::Sketch, i::Int)::StructACSet
    return crel_to_cset(S, es[i][1])[1]
end
"""Get ids that need to be fired"""
function get_premodel_ids(es::EnumState; sketch::Union{Nothing,Sketch}=nothing,
                          maxsize::Int=0)::Vector{Int}
  is = [i for (i,s) in enumerate(es.sizes) if maxsize==0 || s <= maxsize]
  return setdiff(is, es.models ∪ keys(es.branch) ∪ es.failed ∪ keys(es.fired))
end

function get_premodel(es::EnumState, S::Sketch, i::Int)::Tuple{StructACSet, Defined}
  modl, d = es.premodels[es.pk[i]]
  return (crel_to_cset(S, modl)[1], d)
end

function set_failed(es::EnumState, pid::Int, f::Bool)::Nothing
  if f
    push!(es.failed, pid)
  end
  return nothing
end

function add_branch(es::EnumState, S::Sketch, choice::String,
                    chased_premodel_id::Int, chosen_premodel::StructACSet,
                    d::Defined)::Int
  new_id = add_premodel(es, S, chosen_premodel, d)
  push!(es.branch[chased_premodel_id], new_id=>choice)
  return new_id
end


function add_model(es::EnumState, S::Sketch, relm::StructACSet,
                    d::Defined, parent::Int;
                    relm_hsh::Union{UInt64, Nothing}=nothing)::Int
  _, partial = crel_to_cset(S, relm) # fail if nonfunctional
  !partial || error("adding a partial model")
  pid = add_premodel(es, S, relm, d; parent=parent, chash=relm_hsh)
  push!(es.models, pid)
  return pid
end

# DB
######
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
                     ("def", "TEXT", false),
                     ("failed", "BOOLEAN", false),
                     ("size", "INTEGER", false),], FK_["Sketch"]),
    Tab("Model", [("hash", "DECIMAL(20,0)", true),
                  ("jdump", "TEXT", true)], FK_["Premodel"]),
    Tab("Choice", [("delta", "TEXT", false)], FK_[ "parent"=>"Premodel",
      "child" => "Premodel"], ["delta", "parent", "child"]),
    Tab("Fired", Attr_[], FK_["parent"=>"Premodel", "child" => "Premodel"],
      ["parent", "child"])
      ]

function init_db(; reset::Bool=false)::Db
  conn = LibPQ.Connection("dbname=models")
  if reset
    for t in reverse(tabs)
      execute(conn, "DROP TABLE IF EXISTS $(t.name)")
    end
    for t in tabs
      add_tab(t, conn)
    end
  end
  return Db(conn)
end

function set_failed(db::Db, pid::Int, f::Bool)::Nothing
  execute(db.conn, "UPDATE Premodel SET failed = \$2 WHERE Premodel_id=\$1",
          [pid, f])
  return nothing
end

"""Add Sketch (if not already in DB) and return id"""
function add_sketch(db::Db, F::Sketch)::Int
  ghash = hash(F)
  # check if already in db
  r = columntable(execute(db.conn, "SELECT Sketch_id FROM Sketch WHERE hash=\$1",
                          [ghash]))
  if !(isempty(r[:sketch_id]))
    return r[:sketch_id][1]
  end

  z = columntable(execute(db.conn,
    "INSERT INTO Sketch (hash, name, jdump) VALUES (\$1,\$2,\$3) " *
    "RETURNING Sketch_id", [ghash,F.name,to_json(F)]))[:sketch_id][1]
  return z
end

"""Get Sketch by primary key id"""
function get_sketch(db::Db, i::Int)::Sketch
  msg = "SELECT jdump FROM Sketch WHERE Sketch_id=\$1"
  z = columntable(execute(db.conn, msg,[i]))
  return sketch_from_json(z[:jdump][1])
end

"""Add the result of a `chase_step_db` step"""
function add_branch(db::Db, S::Sketch, choice::String,
                   chased_premodel_id::Int, chosen_premodel::StructACSet,
                   d::Defined)::Int
  new_id = add_premodel(db, S, chosen_premodel, d)
  msg = "INSERT INTO Choice(parent, child, delta) VALUES(\$1, \$2, \$3)"
  execute(db.conn, msg * " ON CONFLICT DO NOTHING",
          [chased_premodel_id, new_id, string(choice)])
  return new_id
end

"""Add premodel (if it doesn't exist) """
function add_premodel(db::Db, F::Sketch, m::StructACSet, d::Defined;
                      parent::Union{Int, Nothing}=nothing,
                      chash::Union{UInt64, Nothing}=nothing)::Int
  # println("\t adding premodel $m")
  chash = isnothing(chash) ? hash(nauty(m)) : chash
  # check if already in db
  r_ = columntable(execute(db.conn,
    "SELECT Premodel_id FROM Premodel WHERE hash=\$1",[chash]))[:premodel_id]
  if isempty(r_)
    fid = add_sketch(db, F)
    jsn = generate_json_acset(m)
    dstr = join(d[1],",") * "|" * join(d[2], ",")
    r, = columntable(execute(db.conn,
      """INSERT INTO Premodel (hash, jdump, def, Sketch_id, size)
         VALUES (\$1,\$2, \$3, \$4, \$5) RETURNING Premodel_id""",
            [chash, jsn, dstr, fid, relsize(F, m)]))[:premodel_id]
  else
    r, = r_
  end

  if parent isa Int # Add parents if any
    msg = "INSERT INTO Fired(parent, child) VALUES(\$1, \$2)"
    execute(db.conn, msg * " ON CONFLICT DO NOTHING", [parent, r])
  end
  return r
end

"""Add a premodel that is a model (if not already there). Return id"""
function add_model(db::Db, F::Sketch, relm::StructACSet,
                   d::Defined, parent::Int;
                   relm_hsh::Union{UInt64, Nothing}=nothing)::Int
  m, partial = crel_to_cset(F, relm) # fail if nonfunctional
  !partial || error("adding a partial model")
  pid = add_premodel(db, F, relm, d; parent=parent, chash=relm_hsh)

  # check if already in db
  chash = hash(nauty(m))
  r = columntable(execute(db.conn, "SELECT Model_id FROM Model WHERE hash=\$1",
                              [chash]))[:model_id]
  if !(isempty(r))
    return r[1]
  end

  z = columntable(execute(db.conn, """INSERT INTO Model (hash, jdump, Premodel_id)
                                 VALUES (\$1,\$2,\$3) RETURNING Model_id""",
                          [chash, generate_json_acset(m), pid]))[:model_id]
  return z[1]
end

"""Get premodel id if it exists from the premodel itself (which is hashed)"""
function get_premodel_id(db::Db, crel::StructACSet,
                         crel_pres::Presentation)::Union{Nothing, Int}
  z = columntable(execute(db.conn, """SELECT Premodel_id FROM Premodel
      WHERE hash=\$1""",[hash(nauty(crel))]))[:premodel_id]
  return (isempty(z) ? nothing : z[1])
end


"""Get premodel (as a cset, not crel) by primary key ID"""
function get_premodel(db::Db, S::Sketch, i::Int)::Tuple{StructACSet, Defined}
  modl = parse_json_acset(S.crel, z[:p][1])
  obfun = split(z[:def][1], "|") # bad news if someone names a table with |
  obs, funs = [Set(Symbol.(split(x, ","))) for x in obfun]
  return (sketch, crel_to_cset(S, modl)[1], obs=>funs)
end

"""Get Model by primary key ID"""
function get_model(d::Db, S::Sketch, i::Int)::StructACSet
  z = columntable(execute(d.conn, """SELECT Model.jdump as p
    FROM Model USING (Premodel_id) WHERE Model_id=\$1""", [i]))
  cset = parse_json_acset(S.cset, z[:p][1])
  return sketch => cset
end

function get_models(db::DBLike, S::Sketch;
                    maxsize::Int=0)::Vector{StructACSet}
  [get_model(db, S, i) for i in get_model_ids(db,S;maxsize=maxsize)]
end

function get_model_ids(db::Db, S::Sketch; maxsize::Int
                      )::Vector{Int}
  !isnothing(S) || error("Need sketch to get models from DB")
  q = """SELECT Model.model_id FROM Premodel
         JOIN Model USING (Premodel_id) JOIN Sketch USING (Sketch_id)
         WHERE name='$(S.name)' AND size <= $maxsize ORDER BY size"""
  return Int.(columntable(execute(db.conn, q))[:model_id])
end

"""All premodel hashes for an Sketch that have been chased"""
function get_seen(db::Db, sketch::Sketch, fired::Bool=false;
                  maxsize::Int=0)::Set{UInt64}
  fid = add_sketch(db.conn, sketch)
  wc1 = maxsize == 0 ? "" : " AND size < $maxsize"
  wc2 = fired ? " AND fired" : ""
  msg = "SELECT hash FROM Premodel WHERE Sketch_id=\$1"*wc1*wc2
  z = columntable(execute(db.conn, msg, [fid]))
  return Set(map(UInt64, z[:hash]))
end

function get_premodel_ids(db::Db; sketch::Union{Nothing,Sketch}=nothing,
                          maxsize::Int=0)::Vector{Int}
  !isnothing(sketch) || error("Need sketch to get premodels from Db")
  fid = add_sketch(db, sketch)
  wc1 = maxsize == 0 ? "" : " AND size <= $maxsize"
  wc2 = unchased ? """ AND failed IS NULL""" : ""
  msg = "SELECT Premodel_id FROM Premodel WHERE Sketch_id=\$1"*wc1*wc2
  z = columntable(execute(db.conn, msg * " ORDER BY size", [fid]))
  return collect(z[:premodel_id])
end


function get_premodels(db::Db, sketch::Sketch; maxsize::Int=0
                      )::Vector{StructACSet}
  [get_premodel(db, Int64(i))[2] for i
   in get_premodel_ids(db, sketch; maxsize=maxsize)]
end
end  # module