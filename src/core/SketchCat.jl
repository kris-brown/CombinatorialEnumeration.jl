module SketchCat
export SketchMorphism, mkSketchMorphism, toLabeledSketchCSetHom
using Catlab, Catlab.CategoricalAlgebra, Catlab.Theories
import Catlab.Theories: id, dom, codom
using ..SketchCSets, ..Sketches, ..LGraphs

"""A category of sketches"""

# Sketch morphisms
##################



function LabeledFinCatCSetToLG(X::LabeledFinCatCSet)
  lg = LGraph()
  copy_parts!(lg, X; Dict(:V=>vertices(X), :E=>setdiff(edges(X), refl(X)))...)
  return lg
end



mkFinCatGraph(S::Sketch) = mkFinCatGraph(S.Schema)
struct SketchMorphism
  dom::Sketch
  codom::Sketch
  f::FinFunctor
  function SketchMorphism(d,c,fob,fhom=nothing)
    # (co)cones/eqs check?
    f = FinFunctor(fob,fhom,mkFinCatPresentation.([d,c])...)
    is_functorial(f) || error("f $f")
    return new(d,c,f)
  end
end

function toLabeledSketchCSetHom(F::SketchMorphism)
  c,cd = mkLabeledSketchCSet.([dom(F), codom(F)])
  vmap = Dict{Symbol,Symbol}([k=>Symbol(v) for (k,v) in collect(F.f.ob_map)])
  get_id(Y,v) = Y[only(incident(Y, Symbol(v), :vlabel)), [:refl,:elabel]]
  emap = Dict{Symbol,Symbol}(map(collect(F.f.hom_map)) do (c_hom, cd_hom)
    if typeof(cd_hom).parameters[1] == :id
      return c_hom => get_id(cd,only(cd_hom.args))
    else
      return c_hom => Symbol(cd_hom)
    end
  end)
  imap = Dict{Symbol,Symbol}([get_id(c,k)=>get_id(cd,v) for (k,v) in collect(F.f.ob_map)])
  tcs = (Label=FinFunction(merge(vmap,emap,imap)),)
  return only(homomorphisms(c,cd; type_components=tcs))
end

function mkSketchMorphism(f::ACSetTransformation)

  ds,cds = Sketch.([dom(f),codom(f)])

  dnonrefl = setdiff(edges(dom(f)), dom(f)[:refl])
  cdrefl = Dict([v=>i for (i,v) in enumerate(codom(f)[:refl])])
  cdnonrefl = setdiff(edges(codom(f)), collect(keys(cdrefl)))
  emap = map(collect(f[:E])) do e
    if haskey(cdrefl,e) return Path([], cdrefl[e], cdrefl[e])
    else return findfirst(==(e), cdnonrefl)
    end
  end
  fob = Dict(zip(dom(f)[:vlabel], codom(f)[f[:V]|>collect, :vlabel]))
  non_id = setdiff(edges(dom(f)), dom(f)[:refl])
  fhom = Dict(zip(dom(f)[non_id,:elabel], codom(f)[f[:E](non_id)|>collect, :elabel]))
  return SketchMorphism(ds,cds,fob, fhom)
end

@instance ThCategory{Sketch, SketchMorphism} begin
  dom(f::SketchMorphism) = f.dom
  codom(f::SketchMorphism) = f.codom
  id(A::Sketch) = SketchMorphism(A, A, id(FinCat(dom(A))))
  function compose(f::SketchMorphism, g::SketchMorphism; strict::Bool=false)
    !strict || codom(f) == dom(g) ||
      error("Domain mismatch in composition: $(codom(f)) != $(dom(g))")
    SketchMorphism(dom(f), codom(g), compose(f.f, g.f))
  end
end

end # module 