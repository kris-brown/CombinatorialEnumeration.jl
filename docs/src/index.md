# CombinatorialEnumeration.jl

This package implements a constrained search algorithm, with constraints
specified in the language of category theory. Formally, given a finite (co)-
limit sketch, we enumerate its models up to isomorphism.

## Models
For our purposes, a *model* is an instance of a relational database, i.e. a
collection of tables with foreign keys between them. Normally, one can stick
whatever data one wants into the tables of a database. Suppose our schema is
E⇉V. If we enumerate models on this schema, we will obtain all directed
multi-graphs. Here are the first few:

[todo]

However, we might wish to enumerate the smallest groups:

[todo]

There is no correspondence between groups and databases. At best, every group
can be represented by a certain database instance, but only a very select few
database instances on that schema are actually groups. If we tried to enumerate
the databases that might be groups of order 10 and then filter those which are
actually groups, we would have to enumerate 10^... This isn't feasible, so we
need to incorporate our constraints into the search process. The language of
finite limit sketches allows us to say how we wish to restrict which databases
are valid models.

## Finite (co)limit sketches

A sketch contains a schema, just like a relational database. However, it
contains three kinds of extra data which constrain models.

### Path Equations
We can assert that sequences of foreign keys in a database must yield the same
result. An example of this is the case of reflexive graphs.

We add to our schema a designated `refl` edge for each vertex. The equalities:
- `refl; src = idᵥ`
- `refl; tgt = idᵥ`

Capture the fact that a database with a vertex whose reflexive edge starts or
ends at a different vertex is *not* a valid model.

### Cone objects

A sketch can designated a particular object to satisfy the *cone* constraint.
This constraint says that the elements of that table are in bijection with
matches of some pattern found elsewhere in the database. A pullback is the
classic example of this: we want to identify pairs that agree on a certain
value. For example, a database might have:

[CTS type example]

To enforce that the _ table actually contains the intended content, we assert it
is in bijection with the following pattern.

[todo]

There are many more examples that can show off the versatility of cone
constraints.

### Cocone objects

The last type of constraint available is that of cocones. A cocone object is
asserted to be in bijection with certain equivalence classes (i.e. partitions,
quotients) of the objects in a diagram. A pushout is the classic example of
this: we wish to glue together two tables in our database along a common
boundary.

[example]



## Compositionality

This peculiar language of constraints has an advantage that comes from the fact
that sketches can be related to each other (there is a *category* of sketches).
This means that, for example, gluing sketches together can be a meaningful
operation - if we have computed the models for the individual components, then
a very efficient operation can construct the composite models, rather than
starting from scratch.