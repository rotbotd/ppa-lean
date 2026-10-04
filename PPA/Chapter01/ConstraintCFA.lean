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

def merge (left right : Flow) : Flow :=
  left.foldr List.insert right

def add (abstraction : Abstraction) (flow : Flow) : Flow :=
  List.insert abstraction flow

def whenPresent
    (trigger : Abstraction) (known contribution : Flow) : Flow :=
  if known.contains trigger then contribution else []

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

end State

private def iterate : Nat → (State → State) → State → State
  | 0, _, value => value
  | count + 1, next, value => next (iterate count next value)

def exampleSolution : State :=
  iterate 8 State.step State.empty

theorem example_is_fixed : State.step exampleSolution = exampleSolution :=
  rfl

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
