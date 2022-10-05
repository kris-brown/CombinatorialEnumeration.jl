module SketchLimits
using Catlab.CategoricalAlgebra.CSets: limit!, ACSetLimit


# Limits
########

"""
Take a pullback of attributed C-Sets with a *fixed*, predetermined
transformation on attributes. This looks a lot like a limit (though technically
is not one) where we know ahead of time what the type_components of the
resulting limit legs should be. To assign attributes on the apex, we take the
intersection of the preimages of the provided type components and fail if it
does not produce a unique value.
"""
function limit(::Type{Tuple{ACS,Hom}},diagram; tcs=nothing) where
    {S, Ts, ACS <: StructACSet{S,Ts}, Hom <: LooseACSetTransformation}
  (tcs isa AbstractVector) || error("Must provide tcs")
  limits = map(limit, unpack_diagram(diagram, all=false))
  Xs = cone_objects(diagram)
  Y = ACS()
  result = limit!(Y, diagram, Xs, limits)
  for (f, c, d) in zip(attr(S), adom(S), acodom(S))
    c_legs = collect.(legs(limits[c]))
    Yf = map(zip([X[l, f] for (X, l) in zip(Xs, c_legs)]...)) do vals
      only(intersect([preimage(tc[d], v) for (tc, v) in zip(tcs, vals)]...))
    end
    set_subpart!(Y, f, collect(Yf))
  end
  fixed_cone = Multispan(map(zip(tcs,result.cone)) do (tc, l)
    LooseACSetTransformation(components(l), tc, dom(l), codom(l))
  end)
  ACSetLimit(result.diagram, fixed_cone, result.limits)
end