module CoequalizerSketch
export Coequalizer

using ...Core

using ..EqualizerSketch

Coequalizer = dual(Equalizer, [:E=>:C, :e=>:c])

end # module
