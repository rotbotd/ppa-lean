import TransportSpan

/-!
The order-theoretic argument on PPA Chapter 1, pp. 34--37 of the authors'
transparencies.

This file separates two claims which are easy to blur:

* monotonicity makes iteration from the empty set ascend and keeps every
  iterate below every fixed point;
* finiteness supplies an index where two adjacent iterates coincide.

The theorem below consumes that convergence witness and returns the least
fixed point. A later finite-set module must construct the witness; it is not
smuggled into the definition of iteration as fuel.
-/

namespace PPA.Chapter01.LeastFixedPoint

abbrev Powerset (α : Type) := α → Prop

namespace Powerset

def empty : Powerset α := fun _ => False

def Subset (lower upper : Powerset α) : Prop :=
  ∀ element, lower element → upper element

end Powerset

open Powerset

def Monotone (function : Powerset α → Powerset α) : Prop :=
  ∀ {lower upper}, Subset lower upper → Subset (function lower) (function upper)

def iterate (function : Powerset α → Powerset α) : Nat → Powerset α
  | 0 => empty
  | step + 1 => function (iterate function step)

def IsFixed (function : Powerset α → Powerset α) (candidate : Powerset α) : Prop :=
  function candidate = candidate

def IsLeastFixed
    (function : Powerset α → Powerset α)
    (candidate : Powerset α) : Prop :=
  IsFixed function candidate ∧
    ∀ other, IsFixed function other → Subset candidate other

/-!
A finite powerset gets this certificate by taking `rank` to be cardinality and
`bound` to be the size of its carrier. Stating the exact property here keeps
the termination proof independent of a particular finite-set container: every
strict inclusion consumes at least one unit of the finite height.
-/
structure HeightBound (α : Type) where
  rank : Powerset α → Nat
  bound : Nat
  bounded : ∀ candidate, rank candidate ≤ bound
  strictGrowth : ∀ {lower upper},
    Subset lower upper → lower ≠ upper → rank lower < rank upper

private theorem empty_subset (other : Powerset α) : Subset empty other :=
  fun _ impossible => False.elim impossible

/-- Monotonicity gives the ascending Kleene chain drawn on p. 36. -/
theorem iterate_grows
    (function : Powerset α → Powerset α)
    (monotone : Monotone function) :
    ∀ step, Subset (iterate function step) (iterate function (step + 1))
  | 0 => empty_subset (function empty)
  | step + 1 => monotone (iterate_grows function monotone step)

/-- Every iterate from `∅` remains below every fixed point. -/
theorem iterate_below_fixed
    (function : Powerset α → Powerset α)
    (monotone : Monotone function) :
    ∀ step other, IsFixed function other →
      Subset (iterate function step) other
  | 0, other, _ => empty_subset other
  | step + 1, other, fixed =>
      fun element present =>
        transport {
          (function other) element ->
          other element
        } fixed
          (monotone
            (iterate_below_fixed function monotone step other fixed)
            element
            present)

/-- If no adjacent iterates agree, each round consumes one unit of height. -/
private theorem rank_after_steps
    (function : Powerset α → Powerset α)
    (monotone : Monotone function)
    (height : HeightBound α)
    (neverConverges : ∀ step,
      iterate function step ≠ iterate function (step + 1)) :
    ∀ count,
      height.rank (iterate function 0) + count ≤
        height.rank (iterate function count)
  | 0 => Nat.le_refl _
  | count + 1 =>
      calc
        height.rank (iterate function 0) + (count + 1) ≤
            height.rank (iterate function count) + 1 :=
          Nat.succ_le_succ
            (rank_after_steps function monotone height neverConverges count)
        _ ≤ height.rank (iterate function (count + 1)) :=
          Nat.succ_le_of_lt
            (height.strictGrowth
              (iterate_grows function monotone count)
              (neverConverges count))

/-- Finite height turns the ascending chain into an actual convergence index. -/
theorem finite_height_converges
    (function : Powerset α → Powerset α)
    (monotone : Monotone function)
    (height : HeightBound α) :
    ∃ step, iterate function step = iterate function (step + 1) :=
  Classical.byContradiction fun noConvergence =>
    let neverConverges : ∀ step,
        iterate function step ≠ iterate function (step + 1) :=
      not_exists.mp noConvergence
    let tooManyStrictSteps :=
      rank_after_steps function monotone height neverConverges
        (height.bound + 1)
    Nat.not_succ_le_self height.bound
      (calc
        height.bound + 1 ≤
            height.rank (iterate function 0) + (height.bound + 1) :=
          Nat.le_add_left
            (height.bound + 1)
            (height.rank (iterate function 0))
        _ ≤ height.rank (iterate function (height.bound + 1)) :=
          tooManyStrictSteps
        _ ≤ height.bound :=
          height.bounded (iterate function (height.bound + 1)))

/--
Once adjacent iterates coincide, that iterate is not merely a fixed point: it
is below every other fixed point, hence the least one.
-/
theorem converged_is_least_fixed
    (function : Powerset α → Powerset α)
    (monotone : Monotone function)
    (step : Nat)
    (converged : iterate function step = iterate function (step + 1)) :
    IsLeastFixed function (iterate function step) :=
  ⟨converged.symm,
    fun other fixed =>
      iterate_below_fixed function monotone step other fixed⟩

/-- The book's complete Kleene-iteration claim for a finite-height domain. -/
theorem finite_height_reaches_least_fixed
    (function : Powerset α → Powerset α)
    (monotone : Monotone function)
    (height : HeightBound α) :
    ∃ step, IsLeastFixed function (iterate function step) :=
  match finite_height_converges function monotone height with
  | ⟨step, converged⟩ =>
      ⟨step, converged_is_least_fixed function monotone step converged⟩

end PPA.Chapter01.LeastFixedPoint
