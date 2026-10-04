# Log

## 2026-10-03 — chapter 1 source and boundary

- The formalization follows the book chapter by chapter rather than extracting
  a freestanding abstract-interpretation library.
- Archived the authors' 2005 Chapter 1 transparencies outside Git at
  `/root/.cache/lynn/ppa/chapter1-slides.pdf`. Source:
  `https://cs.nju.edu.cn/_upload/tpl/00/aa/170/template170/analysis/slides1.pdf`.
  SHA-256:
  `534b798d3936844ade8e2ad764a1c87cd43bbf9f4d37d1c8211446c1c6eae9b3`.
- The first vertical slice is Section 1.3's reaching-definitions example:
  labelled `WHILE`, the kill/gen assignment transfer, and its local semantic
  soundness argument. Its executable equation system must reproduce the
  book's best solution, including the two back-edge definitions at the loop
  head. No tactic proof is accepted in the project source.
- Chapter 1 remains open until its four sampler approaches and their shared
  fixed-point machinery are represented.
- The executable table uses twelve named entry/exit components and a
  simultaneous equation step. Kernel reduction checks that iteration reaches
  a fixed point, that the loop entry contains `(y,5)` and `(z,4)` and exactly
  five facts, and that label 6 kills both older `y` facts. `Facts.assign_denotes`
  proves the list implementation is exactly the predicate-level kill/gen
  equation rather than a parallel unverified implementation.

## 2026-10-03 — monotone iteration

- Formalized pp. 34--36 of the Chapter 1 transparencies directly over
  predicate powersets: subset, monotonicity, iteration from `∅`, fixed points,
  and least fixed points.
- `iterate_grows` constructs the ascending chain. `iterate_below_fixed`
  recursively proves each iterate is below any fixed point; its only rewrite
  is an explicit `Eq.mp` along the fixed-point equality.
- `converged_is_least_fixed` consumes `fⁿ(∅) = fⁿ⁺¹(∅)` and returns the
  least-fixed-point statement. This deliberately does not use the executable
  solver's fuel as a termination argument. The remaining edge is the book's
  finiteness/ascending-chain proof and its connection to the twelve-component
  equation system.

## 2026-10-03 — visible transport dependency

- Published the previously local `transport-span` library at
  `https://github.com/rotbotd/lean-transport-span`, pinned PPA to commit
  `c415425`, and replaced the raw `Eq.mp`/`Eq.mpr` transports in the current
  chapter with visible source-to-target spans.
- `iterate_below_fixed` now shows the exact move from
  `(function other) element` to `other element`. `assign_sound` shows the
  generated or preserved branch fact moving to the concrete conditional
  selected by `LastWriter.write`.
- Passing `(if_pos same).symm` directly lost the unreduced conditional in the
  inferred equality type, so the span could no longer identify its target.
  Giving each branch equality an explicit local type retains both endpoints;
  this is a real elaboration boundary rather than a kernel issue.
- A copied flake input initially made Lake delete the dependency and attempt a
  network clone because its manifest still described a Git source. The Nix
  build now rewrites only its sandbox copy of `lakefile.toml` to a path
  dependency, regenerates the sandbox manifest, and builds the exact source
  pinned by `flake.lock`. Ordinary Lake users retain the public Git dependency.
- `lake build` and `nix flake check` both pass.

## 2026-10-04 — finite height forces convergence

- Added `HeightBound`: a natural-valued rank, a global bound, and the claim
  that every strict inclusion strictly raises the rank. For a finite
  powerset, cardinality and the carrier size supply exactly this certificate.
- `rank_after_steps` proves by recursion that if no two adjacent Kleene
  iterates agree, `n` rounds raise the rank by at least `n`.
  `finite_height_converges` runs that claim for `bound + 1` rounds and obtains
  the concrete contradiction `bound + 1 ≤ bound`.
- `finite_height_reaches_least_fixed` composes the new termination result with
  the existing minimality proof. The theorem now contains the whole argument
  on slides 34--36: monotone ascent, finite convergence, and leastness.
- This deliberately does not yet assert that the executable twelve-component
  table is an instance. Its finite fact universe and the denotation of the
  simultaneous table step remain the next bridge.
- No tactic blocks were introduced. `lake build` and `nix flake check` pass.
- The first term-mode version nested `Nat.le_trans`, `Nat.succ_le_succ`, and
  `Nat.succ_le_of_lt`; it checked but hid the induction behind inequality
  plumbing. Replaced both transitivity trees with `calc` chains which display
  every intermediate bound. `calc` still elaborates to a term and introduces
  no tactic proof.

## 2026-10-04 — the twelve equations are monotone

- Defined membership inclusion for executable `Facts` and proved it is
  preserved by `merge`, `kill`, and `assign`. The `merge` proof is an exact
  recursive membership equivalence for the existing duplicate-removing
  implementation; the executable representation was not changed merely to
  make the proof shorter.
- Lifted inclusion to all twelve fields of `Table` and proved `Table.step`
  monotone field by field. This is the concrete equation operator from the
  book, not a parallel abstract function asserted to agree later.
- Changed the private iterator from accumulator recursion to the displayed
  mathematical recurrence `f(iterate n f x)`. The computed result and all
  reduction checks are unchanged, while the ascending-chain induction is now
  definitionally aligned with the book.
- Proved every concrete iterate lies below every fixed table. The induction's
  final equality move uses `transport-span` to display the change from
  inclusion below `Table.step other` to inclusion below `other`.
- `example_is_least_fixed` now proves the 24-round table is below every other
  fixed solution in addition to checking stability by reduction. Deriving the
  round bound from the finite reachable fact universe remains open.
- There are still no tactic blocks. `lake build` and `nix flake check` pass.

## 2026-10-04 — constraint-based CFA begins

- Started Section 1.4 with the exact smaller source program from slides
  46--53, rather than inventing a cleaner example. `ConstraintCFA.State` has
  the four environment components `R(x), R(y), R(f), R(g)` and seven cache
  components `C(1)..C(7)`.
- `State.step` directly implements the four unconditional constraints and
  eight guarded application consequences. Each guard tests whether `f` or
  `g` is present at the operator label, then propagates the argument cache to
  the formal parameter and the body cache to the result label.
- Eight synchronous rounds reduce to a stable state. Kernel reduction checks
  the discriminating entries of the best solution: `g ∈ C(1)`,
  `f ∉ C(1)`, `f ∈ C(5)`, `g ∈ R(x)`, and `R(y) = ∅`. These distinguish the
  best solution from the deliberately over-approximated table on slide 40.
- This slice states and computes the constraint operator; its inclusion
  monotonicity and leastness proof remain open rather than being inherited by
  assertion from the reaching-definitions operator.
