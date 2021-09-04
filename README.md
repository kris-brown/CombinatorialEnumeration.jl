# ModelEnumeration.jl

## Motivation
Suppose you are given a formally specified theory, for example the theory of (small) [categories](https://www.math3ma.com/blog/what-is-a-category), which say a *category* `C` is specified by:
- A set of *objects*, `Ob(C)`
- For each pair of objects `a,b ∈ Ob(C)`, a set of arrows `Hom(a,b)`.
- A composition operator that gives an arrow in `f⋅g ∈ Hom(a,c)` for each pair of arrows `f ∈ Hom(a,b)` and `g ∈ Hom(b,c)`.
- An identity arrow `id(a) ∈ Hom(a,a)` for each object `a ∈ Ob(C)`
- Furthermore, this data must satisfy some constraints:
  - Unitality: `id(a)⋅f = f = f⋅id(b)` for each `f ∈ Hom(a,b)`
  - Associativity: `(f⋅g)⋅h = f⋅(g⋅h)` for each triple of composable arrows.

Even if each individual piece of data or constraint in this definition is straightforward, definitions might seem overwhelming at first insofar as we come across the following types of problems:
  - What are the 5 simplest categories?
  - Given this proposed category, is it actually a category?
  - Are there any categories (bounded by some max size) such that some property `ϕ` holds?

There is pedagogical value in working through these types of problems in one's head, but there is also value in having these answers automatically ready at hand when trying to think about / build intuition for more complicated concepts. There is something mechanical about this process, and the purpose of this repo is to mechanize precisely that in an efficient way that's also usable for people trying to build their intuitions.

## Usage

TBD

## Wishlist
- [x] Generate models of a theory by a variant of [the chase](https://en.wikipedia.org/wiki/Chase_(algorithm)) that deliberately produces models that are not initial.
- [x] Store model progress in a Postgres database
- [ ] Test properties of the various theories in the `data/sketches/` directory
- [ ] Automatically convert the `EqTheories` (intuitively declarable through wiring diagrams from the `@program` macro, see `src/old/ATP/WD.jl`) into the finite limit theories of `src/FLS.jl`.
- [ ] Use `@threads` to parallelize many parallelizable aspects of the code.
- [ ] Apply known relationships between theories to reduce the computational burden. I.e. models of theory `T` that is just theory `V` with extra constraints can be found by filtering `V` models (if they were already computed). If theory `T` is the pushout of smaller theories `A` and `B`, then solve for the small models and take the join (in the SQL sense, joining on overlapping variables) of the two sets of models.
- [ ] Friendly text-based API