# PPA in term-mode Lean

A chapter-by-chapter formalization of Flemming Nielson, Hanne Riis Nielson,
and Chris Hankin's *Principles of Program Analysis*.

The source order is part of the project: later abstractions do not replace the
worked analyses which motivate them. Proofs use explicit Lean terms rather
than tactics. Each chapter has:

1. the definitions introduced by the book;
2. a worked analysis taken from the book;
3. a kernel-checked correctness argument before the next chapter begins.

Chapter 1 is in progress. Its first slice defines the labelled `WHILE`
language and the assignment transfer function for reaching definitions. It
then runs the twelve equations for the book's six-label example to a fixed
point and checks the exact loop-entry and final-assignment facts. The local
soundness proof exposes every case as an ordinary term; a separate theorem
connects the executable list operation to that predicate-level equation.

## Check

```console
lake build
nix flake check
```
