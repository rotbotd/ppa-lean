# PPA in term-mode Lean

A chapter-by-chapter formalization of Flemming Nielson, Hanne Riis Nielson,
and Chris Hankin's *Principles of Program Analysis*.

The source order is part of the project: later abstractions do not replace the
worked analyses which motivate them. Proofs use explicit Lean terms rather
than tactics. Equality transport uses the separately checked
[`transport-span`](https://github.com/rotbotd/lean-transport-span) elaborator,
so the source and destination propositions remain visible at each rewrite:

```lean
transport { (function other) element -> other element } fixed present
```

The elaborator emits `Eq.mp (congrArg ...)`; Lean's kernel still checks the
ordinary proof term. Each chapter has:

1. the definitions introduced by the book;
2. a worked analysis taken from the book;
3. a kernel-checked correctness argument before the next chapter begins.

Chapter 1 is in progress. Its first slice defines the labelled `WHILE`
language and the assignment transfer function for reaching definitions. It
then runs the twelve equations for the book's six-label example to a fixed
point and checks the exact loop-entry and final-assignment facts. The local
soundness proof exposes every case as an ordinary term; a separate theorem
connects the executable list operation to that predicate-level equation.
Membership inclusion is proved through `merge`, `kill`, and `assign`, then
lifted field-by-field through all twelve equations. Consequently the actual
computed table is proved to be the least fixed table, not just checked to be
stable.

`LeastFixedPoint.lean` follows the next four pages without appealing to a
library theorem. It constructs the ascending chain from monotonicity, proves
every iterate lies below every fixed point, and turns an explicit adjacent-
iterate equality into the least fixed point. A `HeightBound` certificate then
turns finite height into a convergence index: if every round were strict, its
bounded rank would rise past its own bound. Connecting that generic argument
to the finite fact universe remains explicit work. The twelve-component
operator is already proved monotone and its 24-round result least; the
remaining gap is deriving a convergence bound rather than observing that
this particular round count is stable.

`ConstraintCFA.lean` starts Section 1.4 from the book's own seven-label
lambda-calculus example. Its eleven fields are exactly `R(x)`, `R(y)`,
`R(f)`, `R(g)`, and `C(1)` through `C(7)`; `State.step` is the four
unconditional inclusions plus all eight guarded consequences printed on
pp. 46--51. Iteration recovers the best solution rather than the safe but
imprecise one: the call through `x` contains `g` but not `f`, the outer call
contains `f`, and the constant argument contributes no abstraction. The
guarded propagation operator is proved monotone—including the case where a
guard becomes newly enabled—and the computed state is proved below every
other fixed solution.

`AbstractInterpretation.lean` begins Section 1.5 at the concrete/abstract
boundary rather than at a lattice slogan. A trace records successive variable
definitions; `semanticReaching` keeps its last writer for each variable.
`abstract` unions those facts over a trace set, while `concretize` selects the
traces admitted by a fact set. Their Galois law is proved in both directions,
and the two pictured traces on slide 68 exhibit all five displayed reaching
facts by reduction.

## Check

```console
lake build
nix flake check
```
