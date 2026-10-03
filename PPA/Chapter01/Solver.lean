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

end Table

private def iterate {α : Type} : Nat → (α → α) → α → α
  | 0, _, value => value
  | count + 1, next, value => iterate count next (next value)

/-- Twenty-four synchronous rounds reach the stable table for this graph. -/
def exampleSolution : Table :=
  iterate 24 Table.step Table.empty

/-- The computed table has stabilized: another round changes nothing. -/
theorem example_is_fixed : Table.step exampleSolution = exampleSolution :=
  rfl

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
