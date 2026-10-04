import TransportSpan

/-!
PPA Section 1.4's first constraint-based control-flow analysis.

The source program is the seven-label example from pp. 46--53:

```text
let f = fn x => (x¹ 7²)³
    g = fn y => y⁴
in  (f⁵ g⁶)⁷
```

`R` is represented by the four `r*` fields and `C` by the seven `c*`
fields. One `step` simultaneously adds every unconditional and enabled
conditional contribution from the displayed constraint system.
-/

namespace PPA.Chapter01.ConstraintCFA

inductive Abstraction where
  | f
  | g
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

abbrev Flow := List Abstraction

namespace Flow

def Included (lower upper : Flow) : Prop :=
  ∀ abstraction, abstraction ∈ lower → abstraction ∈ upper

theorem empty_included (upper : Flow) : Included [] upper :=
  fun _ impossible => False.elim (List.not_mem_nil impossible)

def merge (left right : Flow) : Flow :=
  left.foldr List.insert right

def add (abstraction : Abstraction) (flow : Flow) : Flow :=
  List.insert abstraction flow

def whenPresent
    (trigger : Abstraction) (known contribution : Flow) : Flow :=
  if known.contains trigger then contribution else []

theorem mem_merge_iff (abstraction : Abstraction) :
    ∀ left right : Flow,
      abstraction ∈ merge left right ↔
        abstraction ∈ left ∨ abstraction ∈ right
  | [], _ =>
      ⟨fun present => Or.inr present,
        fun alternatives =>
          match alternatives with
          | Or.inl impossible => False.elim (List.not_mem_nil impossible)
          | Or.inr present => present⟩
  | _ :: tail, right =>
      ⟨fun present =>
          match List.mem_insert_iff.mp present with
          | Or.inl here => Or.inl (List.mem_cons.mpr (Or.inl here))
          | Or.inr later =>
              match (mem_merge_iff abstraction tail right).mp later with
              | Or.inl inTail =>
                  Or.inl (List.mem_cons.mpr (Or.inr inTail))
              | Or.inr inRight => Or.inr inRight,
        fun alternatives =>
          match alternatives with
          | Or.inl inLeft =>
              match List.mem_cons.mp inLeft with
              | Or.inl here => List.mem_insert_iff.mpr (Or.inl here)
              | Or.inr inTail =>
                  List.mem_insert_iff.mpr
                    (Or.inr
                      ((mem_merge_iff abstraction tail right).mpr
                        (Or.inl inTail)))
          | Or.inr inRight =>
              List.mem_insert_iff.mpr
                (Or.inr
                  ((mem_merge_iff abstraction tail right).mpr
                    (Or.inr inRight)))⟩

theorem merge_monotone
    {leftLower leftUpper rightLower rightUpper : Flow}
    (leftIncluded : Included leftLower leftUpper)
    (rightIncluded : Included rightLower rightUpper) :
    Included (merge leftLower rightLower) (merge leftUpper rightUpper) :=
  fun abstraction present =>
    (mem_merge_iff abstraction leftUpper rightUpper).mpr
      (match (mem_merge_iff abstraction leftLower rightLower).mp present with
      | Or.inl inLeft => Or.inl (leftIncluded abstraction inLeft)
      | Or.inr inRight => Or.inr (rightIncluded abstraction inRight))

theorem add_monotone
    (abstraction : Abstraction) {lower upper : Flow}
    (included : Included lower upper) :
    Included (add abstraction lower) (add abstraction upper) :=
  fun queried present =>
    List.mem_insert_iff.mpr
      (match List.mem_insert_iff.mp present with
      | Or.inl added => Or.inl added
      | Or.inr previous => Or.inr (included queried previous))

theorem whenPresent_monotone
    (trigger : Abstraction)
    {knownLower knownUpper contributionLower contributionUpper : Flow}
    (knownIncluded : Included knownLower knownUpper)
    (contributionIncluded : Included contributionLower contributionUpper) :
    Included
      (whenPresent trigger knownLower contributionLower)
      (whenPresent trigger knownUpper contributionUpper) :=
  match lowerResult : knownLower.contains trigger,
      upperResult : knownUpper.contains trigger with
  | false, _ =>
      let lowerClosed :
          whenPresent trigger knownLower contributionLower = [] :=
        if_neg (Bool.eq_false_iff.mp lowerResult)
      transport {
        Included [] (whenPresent trigger knownUpper contributionUpper) ->
        Included
          (whenPresent trigger knownLower contributionLower)
          (whenPresent trigger knownUpper contributionUpper)
      } lowerClosed.symm (empty_included _)
  | true, true =>
      let lowerOpen :
          whenPresent trigger knownLower contributionLower =
            contributionLower :=
        if_pos lowerResult
      let upperOpen :
          whenPresent trigger knownUpper contributionUpper =
            contributionUpper :=
        if_pos upperResult
      let lowerRewritten :=
        transport {
          Included contributionLower contributionUpper ->
          Included
            (whenPresent trigger knownLower contributionLower)
            contributionUpper
        } lowerOpen.symm contributionIncluded
      transport {
        Included
          (whenPresent trigger knownLower contributionLower)
          contributionUpper ->
        Included
          (whenPresent trigger knownLower contributionLower)
          (whenPresent trigger knownUpper contributionUpper)
      } upperOpen.symm lowerRewritten
  | true, false =>
      False.elim
        (Bool.noConfusion
          (Eq.trans
            upperResult.symm
            (List.contains_iff_mem.mpr
              (knownIncluded trigger
                (List.contains_iff_mem.mp lowerResult)))))

end Flow

structure State where
  rx : Flow
  ry : Flow
  rf : Flow
  rg : Flow
  c1 : Flow
  c2 : Flow
  c3 : Flow
  c4 : Flow
  c5 : Flow
  c6 : Flow
  c7 : Flow
  deriving BEq, Repr

namespace State

structure Included (lower upper : State) : Prop where
  rx : Flow.Included lower.rx upper.rx
  ry : Flow.Included lower.ry upper.ry
  rf : Flow.Included lower.rf upper.rf
  rg : Flow.Included lower.rg upper.rg
  c1 : Flow.Included lower.c1 upper.c1
  c2 : Flow.Included lower.c2 upper.c2
  c3 : Flow.Included lower.c3 upper.c3
  c4 : Flow.Included lower.c4 upper.c4
  c5 : Flow.Included lower.c5 upper.c5
  c6 : Flow.Included lower.c6 upper.c6
  c7 : Flow.Included lower.c7 upper.c7

def empty : State where
  rx := []
  ry := []
  rf := []
  rg := []
  c1 := []
  c2 := []
  c3 := []
  c4 := []
  c5 := []
  c6 := []
  c7 := []

theorem empty_included (upper : State) : Included empty upper where
  rx := Flow.empty_included upper.rx
  ry := Flow.empty_included upper.ry
  rf := Flow.empty_included upper.rf
  rg := Flow.empty_included upper.rg
  c1 := Flow.empty_included upper.c1
  c2 := Flow.empty_included upper.c2
  c3 := Flow.empty_included upper.c3
  c4 := Flow.empty_included upper.c4
  c5 := Flow.empty_included upper.c5
  c6 := Flow.empty_included upper.c6
  c7 := Flow.empty_included upper.c7

/-!
The four guarded pairs below are the application constraints:

* `g ∈ C1` sends `C2` to `R(y)` and `C4` to `C3`;
* `f ∈ C1` sends `C2` to `R(x)` and `C3` to itself;
* `g ∈ C5` sends `C6` to `R(y)` and `C4` to `C7`;
* `f ∈ C5` sends `C6` to `R(x)` and `C3` to `C7`.
-/
def step (old : State) : State where
  rx := Flow.merge old.rx
    (Flow.merge
      (Flow.whenPresent .f old.c1 old.c2)
      (Flow.whenPresent .f old.c5 old.c6))
  ry := Flow.merge old.ry
    (Flow.merge
      (Flow.whenPresent .g old.c1 old.c2)
      (Flow.whenPresent .g old.c5 old.c6))
  rf := Flow.add .f old.rf
  rg := Flow.add .g old.rg
  c1 := Flow.merge old.c1 old.rx
  c2 := old.c2
  c3 := Flow.merge old.c3
    (Flow.merge
      (Flow.whenPresent .g old.c1 old.c4)
      (Flow.whenPresent .f old.c1 old.c3))
  c4 := Flow.merge old.c4 old.ry
  c5 := Flow.merge old.c5 old.rf
  c6 := Flow.merge old.c6 old.rg
  c7 := Flow.merge old.c7
    (Flow.merge
      (Flow.whenPresent .g old.c5 old.c4)
      (Flow.whenPresent .f old.c5 old.c3))

theorem step_monotone {lower upper : State}
    (included : Included lower upper) :
    Included (step lower) (step upper) where
  rx := Flow.merge_monotone included.rx
    (Flow.merge_monotone
      (Flow.whenPresent_monotone .f included.c1 included.c2)
      (Flow.whenPresent_monotone .f included.c5 included.c6))
  ry := Flow.merge_monotone included.ry
    (Flow.merge_monotone
      (Flow.whenPresent_monotone .g included.c1 included.c2)
      (Flow.whenPresent_monotone .g included.c5 included.c6))
  rf := Flow.add_monotone .f included.rf
  rg := Flow.add_monotone .g included.rg
  c1 := Flow.merge_monotone included.c1 included.rx
  c2 := included.c2
  c3 := Flow.merge_monotone included.c3
    (Flow.merge_monotone
      (Flow.whenPresent_monotone .g included.c1 included.c4)
      (Flow.whenPresent_monotone .f included.c1 included.c3))
  c4 := Flow.merge_monotone included.c4 included.ry
  c5 := Flow.merge_monotone included.c5 included.rf
  c6 := Flow.merge_monotone included.c6 included.rg
  c7 := Flow.merge_monotone included.c7
    (Flow.merge_monotone
      (Flow.whenPresent_monotone .g included.c5 included.c4)
      (Flow.whenPresent_monotone .f included.c5 included.c3))

def IsFixed (candidate : State) : Prop :=
  step candidate = candidate

def IsLeastFixed (candidate : State) : Prop :=
  IsFixed candidate ∧
    ∀ other, IsFixed other → Included candidate other

end State

private def iterate : Nat → (State → State) → State → State
  | 0, _, value => value
  | count + 1, next, value => next (iterate count next value)

theorem example_iteration_grows :
    ∀ count,
      State.Included
        (iterate count State.step State.empty)
        (iterate (count + 1) State.step State.empty)
  | 0 => State.empty_included (State.step State.empty)
  | count + 1 => State.step_monotone (example_iteration_grows count)

theorem example_iteration_below_fixed :
    ∀ count other, State.IsFixed other →
      State.Included (iterate count State.step State.empty) other
  | 0, other, _ => State.empty_included other
  | count + 1, other, fixed =>
      transport {
        State.Included
          (State.step (iterate count State.step State.empty))
          (State.step other) ->
        State.Included
          (State.step (iterate count State.step State.empty))
          other
      } fixed
        (State.step_monotone
          (example_iteration_below_fixed count other fixed))

def exampleSolution : State :=
  iterate 8 State.step State.empty

theorem example_is_fixed : State.step exampleSolution = exampleSolution :=
  rfl

theorem example_is_least_fixed : State.IsLeastFixed exampleSolution :=
  ⟨example_is_fixed,
    fun other fixed => example_iteration_below_fixed 8 other fixed⟩

/-! The four application sites recover the best solution on p. 40. -/
theorem x_application_may_call_g :
    exampleSolution.c1.contains .g = true :=
  rfl

theorem outer_application_may_call_f :
    exampleSolution.c5.contains .f = true :=
  rfl

theorem no_spurious_function_at_x_application :
    exampleSolution.c1.contains .f = false :=
  rfl

theorem argument_reaches_x :
    exampleSolution.rx.contains .g = true :=
  rfl

theorem constant_argument_carries_no_abstraction :
    exampleSolution.ry = [] :=
  rfl

end PPA.Chapter01.ConstraintCFA
