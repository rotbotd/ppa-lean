import PPA.Chapter01.ReachingDefinitions

/-!
An executable copy of the equation system on PPA Chapter 1's six-label
reaching-definitions example. The equations are synchronous: every round reads
one table and produces the next. Iteration therefore exposes the same growth
from `∅` that the chapter draws by hand.
-/

namespace PPA.Chapter01.ReachingDefinitions

open PPA.Chapter01

abbrev Facts := List Definition

namespace Facts

def Included (lower upper : Facts) : Prop :=
  ∀ fact, fact ∈ lower → fact ∈ upper

theorem empty_included (upper : Facts) : Included [] upper :=
  fun _ impossible => False.elim (List.not_mem_nil impossible)

def denotes (definitions : Facts) : DefSet :=
  fun name origin => { name := name, origin := origin } ∈ definitions

def merge (left right : Facts) : Facts :=
  left.foldr List.insert right

def kill (written : Var) (definitions : Facts) : Facts :=
  definitions.filter (fun definition => definition.name != written)

def assign (definitions : Facts) (written : Var) (label : Label) : Facts :=
  List.insert { name := written, origin := some label } (kill written definitions)

def entry : Facts := [
  { name := .x, origin := none },
  { name := .y, origin := none },
  { name := .z, origin := none }
]

theorem mem_merge_iff (fact : Definition) :
    ∀ left right : Facts,
      fact ∈ merge left right ↔ fact ∈ left ∨ fact ∈ right
  | [], _ =>
      ⟨fun present => Or.inr present,
        fun alternatives =>
          match alternatives with
          | Or.inl impossible => False.elim (List.not_mem_nil impossible)
          | Or.inr present => present⟩
  | _ :: tail, right =>
      ⟨fun present =>
          match List.mem_insert_iff.mp present with
          | Or.inl here =>
              Or.inl (List.mem_cons.mpr (Or.inl here))
          | Or.inr later =>
              match (mem_merge_iff fact tail right).mp later with
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
                      ((mem_merge_iff fact tail right).mpr
                        (Or.inl inTail)))
          | Or.inr inRight =>
              List.mem_insert_iff.mpr
                (Or.inr
                  ((mem_merge_iff fact tail right).mpr
                    (Or.inr inRight)))⟩

theorem merge_monotone
    {leftLower leftUpper rightLower rightUpper : Facts}
    (leftIncluded : Included leftLower leftUpper)
    (rightIncluded : Included rightLower rightUpper) :
    Included (merge leftLower rightLower) (merge leftUpper rightUpper) :=
  fun fact present =>
    (mem_merge_iff fact leftUpper rightUpper).mpr
      (match (mem_merge_iff fact leftLower rightLower).mp present with
      | Or.inl inLeft => Or.inl (leftIncluded fact inLeft)
      | Or.inr inRight => Or.inr (rightIncluded fact inRight))

theorem kill_monotone
    (written : Var) {lower upper : Facts}
    (included : Included lower upper) :
    Included (kill written lower) (kill written upper) :=
  fun fact present =>
    let filtered := List.mem_filter.mp present
    List.mem_filter.mpr ⟨included fact filtered.1, filtered.2⟩

theorem assign_monotone
    (written : Var) (label : Label) {lower upper : Facts}
    (included : Included lower upper) :
    Included (assign lower written label) (assign upper written label) :=
  fun fact present =>
    List.mem_insert_iff.mpr
      (match List.mem_insert_iff.mp present with
      | Or.inl generated => Or.inl generated
      | Or.inr survived =>
          Or.inr (kill_monotone written included fact survived))

/-- The executable list transfer denotes exactly the predicate equation. -/
theorem assign_denotes
    (definitions : Facts)
    (written : Var)
    (label : Label)
    (name : Var)
    (origin : Origin) :
    denotes (assign definitions written label) name origin ↔
      DefSet.assign (denotes definitions) written label name origin :=
  ⟨fun present =>
      match List.mem_insert_iff.mp present with
      | Or.inl generated =>
          Or.inr
            ⟨congrArg Definition.name generated,
              congrArg Definition.origin generated⟩
      | Or.inr survived =>
          let filtered := List.mem_filter.mp survived
          Or.inl ⟨bne_iff_ne.mp filtered.2, filtered.1⟩,
    fun valid =>
      match valid with
      | Or.inl preserved =>
          List.mem_insert_iff.mpr
            (Or.inr
              (List.mem_filter.mpr
                ⟨preserved.2, bne_iff_ne.mpr preserved.1⟩))
      | Or.inr generated =>
          List.mem_insert_iff.mpr
            (Or.inl
              (match generated.1, generated.2 with
              | rfl, rfl => rfl))⟩

end Facts

structure Table where
  entry1 : Facts
  exit1 : Facts
  entry2 : Facts
  exit2 : Facts
  entry3 : Facts
  exit3 : Facts
  entry4 : Facts
  exit4 : Facts
  entry5 : Facts
  exit5 : Facts
  entry6 : Facts
  exit6 : Facts
  deriving BEq, Repr

namespace Table

structure Included (lower upper : Table) : Prop where
  entry1 : Facts.Included lower.entry1 upper.entry1
  exit1 : Facts.Included lower.exit1 upper.exit1
  entry2 : Facts.Included lower.entry2 upper.entry2
  exit2 : Facts.Included lower.exit2 upper.exit2
  entry3 : Facts.Included lower.entry3 upper.entry3
  exit3 : Facts.Included lower.exit3 upper.exit3
  entry4 : Facts.Included lower.entry4 upper.entry4
  exit4 : Facts.Included lower.exit4 upper.exit4
  entry5 : Facts.Included lower.entry5 upper.entry5
  exit5 : Facts.Included lower.exit5 upper.exit5
  entry6 : Facts.Included lower.entry6 upper.entry6
  exit6 : Facts.Included lower.exit6 upper.exit6

def empty : Table where
  entry1 := []
  exit1 := []
  entry2 := []
  exit2 := []
  entry3 := []
  exit3 := []
  entry4 := []
  exit4 := []
  entry5 := []
  exit5 := []
  entry6 := []
  exit6 := []

theorem empty_included (upper : Table) : Included empty upper where
  entry1 := Facts.empty_included upper.entry1
  exit1 := Facts.empty_included upper.exit1
  entry2 := Facts.empty_included upper.entry2
  exit2 := Facts.empty_included upper.exit2
  entry3 := Facts.empty_included upper.entry3
  exit3 := Facts.empty_included upper.exit3
  entry4 := Facts.empty_included upper.entry4
  exit4 := Facts.empty_included upper.exit4
  entry5 := Facts.empty_included upper.entry5
  exit5 := Facts.empty_included upper.exit5
  entry6 := Facts.empty_included upper.entry6
  exit6 := Facts.empty_included upper.exit6

/-- One simultaneous application of the twelve equations in Section 1.3. -/
def step (old : Table) : Table where
  entry1 := Facts.entry
  exit1 := Facts.assign old.entry1 .y 1
  entry2 := old.exit1
  exit2 := Facts.assign old.entry2 .z 2
  entry3 := Facts.merge old.exit2 old.exit5
  exit3 := old.entry3
  entry4 := old.exit3
  exit4 := Facts.assign old.entry4 .z 4
  entry5 := old.exit4
  exit5 := Facts.assign old.entry5 .y 5
  entry6 := old.exit3
  exit6 := Facts.assign old.entry6 .y 6

/-- Every equation preserves inclusion in all of its inputs. -/
theorem step_monotone {lower upper : Table}
    (included : Included lower upper) :
    Included (step lower) (step upper) where
  entry1 := fun _ present => present
  exit1 := Facts.assign_monotone .y 1 included.entry1
  entry2 := included.exit1
  exit2 := Facts.assign_monotone .z 2 included.entry2
  entry3 := Facts.merge_monotone included.exit2 included.exit5
  exit3 := included.entry3
  entry4 := included.exit3
  exit4 := Facts.assign_monotone .z 4 included.entry4
  entry5 := included.exit4
  exit5 := Facts.assign_monotone .y 5 included.entry5
  entry6 := included.exit3
  exit6 := Facts.assign_monotone .y 6 included.entry6

def IsFixed (candidate : Table) : Prop :=
  step candidate = candidate

def IsLeastFixed (candidate : Table) : Prop :=
  IsFixed candidate ∧
    ∀ other, IsFixed other → Included candidate other

end Table

private def iterate {α : Type} : Nat → (α → α) → α → α
  | 0, _, value => value
  | count + 1, next, value => next (iterate count next value)

/-- The actual twelve-component table forms the ascending chain from p. 36. -/
theorem example_iteration_grows :
    ∀ count,
      Table.Included
        (iterate count Table.step Table.empty)
        (iterate (count + 1) Table.step Table.empty)
  | 0 => Table.empty_included (Table.step Table.empty)
  | count + 1 => Table.step_monotone (example_iteration_grows count)

/-- Every concrete iterate is below every fixed table. -/
theorem example_iteration_below_fixed :
    ∀ count other, Table.IsFixed other →
      Table.Included (iterate count Table.step Table.empty) other
  | 0, other, _ => Table.empty_included other
  | count + 1, other, fixed =>
      transport {
        Table.Included
          (Table.step (iterate count Table.step Table.empty))
          (Table.step other) ->
        Table.Included
          (Table.step (iterate count Table.step Table.empty))
          other
      } fixed
        (Table.step_monotone
          (example_iteration_below_fixed count other fixed))

/-- Twenty-four synchronous rounds reach the stable table for this graph. -/
def exampleSolution : Table :=
  iterate 24 Table.step Table.empty

/-- The computed table has stabilized: another round changes nothing. -/
theorem example_is_fixed : Table.step exampleSolution = exampleSolution :=
  rfl

/-- The computed stable table is below every other fixed solution. -/
theorem example_is_least_fixed : Table.IsLeastFixed exampleSolution :=
  ⟨example_is_fixed,
    fun other fixed => example_iteration_below_fixed 24 other fixed⟩

/-- Both loop-body assignments reach the loop test through the back edge. -/
theorem loop_entry_contains_back_edge_writers :
    exampleSolution.entry3.contains { name := .y, origin := some 5 } = true ∧
    exampleSolution.entry3.contains { name := .z, origin := some 4 } = true :=
  ⟨rfl, rfl⟩

/-- The loop entry is the five-element best solution shown in the book. -/
theorem loop_entry_has_no_extra_fact :
    exampleSolution.entry3.length = 5 :=
  rfl

/-- Label 6 kills both reaching definitions of `y` and generates `(y, 6)`. -/
theorem final_assignment_result :
    exampleSolution.exit6.contains { name := .y, origin := some 6 } = true ∧
    exampleSolution.exit6.contains { name := .y, origin := some 1 } = false ∧
    exampleSolution.exit6.contains { name := .y, origin := some 5 } = false ∧
    exampleSolution.exit6.length = 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

end PPA.Chapter01.ReachingDefinitions
