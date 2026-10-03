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

end PPA.Chapter01.LeastFixedPoint
