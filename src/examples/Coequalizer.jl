module CoequalizerSketch
export Coequalizer

using ...Sketches

using ..EqualizerSketch

Coequalizer = dual(Equalizer, [:E=>:C, :e=>:c])

end # module
