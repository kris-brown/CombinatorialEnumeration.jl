# ![CombinatorialEnumeration.jl](docs/src/assets/logo.png) CombinatorialEnumeration.jl
[![Documentation](https://github.com/kris-brown/CombinatorialEnumeration.jl/workflows/Documentation/badge.svg)](https://kris-brown.github.io/CombinatorialEnumeration.jl/dev/)
![Tests](https://github.com/kris-brown/CombinatorialEnumeration.jl/workflows/Tests/badge.svg)

This package implements a constrained search algorithm, with constraints
specified in the language of category theory. Formally, given a finite (co)-
limit sketch, we enumerate its models up to isomorphism. See more in the
[documentation](https://kris-brown.github.io/CombinatorialEnumeration.jl/dev/),
and some examples are in the top-level `data/` directory.

## Status
This is very experimental code, so there may be frequent breaking changes. There
is great opportunity for massive speed-ups - really the most basic
implementations to get something running is all that is written so far, but done
so in a modular way (e.g. enforcing cone constraints, enforcing cocone
constraints) so that bottlenecks can be identified and improved piecemeal.
