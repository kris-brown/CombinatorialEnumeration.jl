using Catlab.Present
using Catlab.Graphs.BasicGraphs: TheoryGraph
using Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset

"""Edges and vertices labeled by symbols"""
@present TheoryLabeledGraph <: TheoryGraph begin
  Label::AttrType
  vlabel::Attr(V,Label)
  elabel::Attr(E,Label)
end;

@acset_type LabeledGraph_(TheoryLabeledGraph, index=[:src,:tgt])
const LabeledGraph = LabeledGraph_{Symbol}
struct Cone
  d::LabeledGraph
  apex::Symbol
  legs::Dict{Int, Symbol}
end

struct FLS
  name::Symbol
  schema::LabeledGraph
  cones::Set{Cone}
  eqs::Set{Pair{Vector{Symbol}, Vector{Symbol}}}
end


add_srctgt(x::Symbol) = Symbol("src_$(x)") => Symbol("tgt_$(x)")

function grph_to_crel(name::Symbol,fls::LabeledGraph)::StructACSet
  pres = Presentation(FreeSchema)
  nv = length(fls[:vlabel])
  alledge = vcat([add_srctgt(e) for e in fls[:elabel]]...)
  xobs = [Ob(FreeSchema, s) for s in [fls[:vlabel]...,fls[:elabel]...]]
  for x in xobs
    add_generator!(pres, x)
  end
  for (i,(e, src, tgt)) in enumerate(zip(fls[:elabel],fls[:src], fls[:tgt]))
    s, t = add_srctgt(e)
    add_generator!(pres, Hom(s, xobs[nv+i], xobs[src]))
    add_generator!(pres, Hom(t, xobs[nv+i], xobs[tgt]))
  end
  name_ = Symbol("rel_$name")
  expr = struct_acset(name_, StructACSet, pres, index=alledge)
  eval(expr)
  return Base.invokelatest(eval(name_))
end

function grph_to_cset(name::Symbol, fls::LabeledGraph)::StructACSet
  pres = Presentation(FreeSchema)
  xobs = [Ob(FreeSchema, s) for s in fls[:vlabel]]
  for x in xobs
    add_generator!(pres, x)
  end
  for (e, src, tgt) in zip(fls[:elabel], fls[:src], fls[:tgt])
    add_generator!(pres, Hom(e, xobs[src], xobs[tgt]))
  end
  expr = struct_acset(name, StructACSet, pres, index=fls[:elabel])
  eval(expr)
  return Base.invokelatest(eval(name))
end

