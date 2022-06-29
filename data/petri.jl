using Catlab.Present, Catlab.CategoricalAlgebra, Catlab.Theories
using ModelEnumeration

@present ThPetri(FreeSchema) begin
  (S,T,I,O)::Ob
  si::Hom(S,I)
  os::Hom(O,S)
  it::Hom(I,T)
  to::Hom(T,O)
end
@acset_type Petri(ThPetri)

"""Create all petri nets with i S/T and i+1 I/O"""
function all_petri(i::Int)::Vector{Petri}
  res = Petri[]
  I = Petri()
  add_parts!(I, :S, i);add_parts!(I, :T, i)
  add_parts!(I, :I, i);add_parts!(I, :O, i);
  for os in Iterators.product([1:i for _ in 1:i]...)
    set_subpart!(I, :os, collect(os))
    for it in Iterators.product([1:i for _ in 1:i]...)
      set_subpart!(I, :it, collect(it))
      for si in Iterators.product([1:i for _ in 1:i]...)
        set_subpart!(I, :si, collect(si))
        for to in Iterators.product([1:i for _ in 1:i]...)
          set_subpart!(I, :to, collect(to))
          push!(res, deepcopy(I))
        end
      end
    end
  end
  return res
end

petschema = @acset LabeledGraph begin
  V = 4
  E = 4
  vlabel = [:S,:T,:I,:O]
  elabel = [:is,:it,:os,:ot]
  src    = [3,  3, 4, 4]
  tgt    = [1, 2,  1,  2]
end


psketch = Sketch(:FG, petschema, Cone[], Cone[], [])

es = EnumState()

