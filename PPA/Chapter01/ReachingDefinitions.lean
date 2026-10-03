import PPA.Chapter01.While

/-!
The local transfer step from PPA Section 1.3.

A definition is a variable paired with either the label of its last assignment
or `none`, the book's `?` origin at program entry. `DefSet` is deliberately a
predicate rather than an executable container: this first statement is the
mathematical equation the later solver must implement.
-/

namespace PPA.Chapter01.ReachingDefinitions

open PPA.Chapter01

abbrev Origin := Option Label
abbrev DefSet := Var → Origin → Prop

structure Definition where
  name : Var
  origin : Origin
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

namespace DefSet

def empty : DefSet := fun _ _ => False

def union (left right : DefSet) : DefSet :=
  fun name origin => left name origin ∨ right name origin

def entry : DefSet :=
  fun _ origin => origin = none

/-- Remove every prior definition of `written`. -/
def kill (written : Var) (definitions : DefSet) : DefSet :=
  fun name origin => name ≠ written ∧ definitions name origin

/-- Add the definition made by the labelled assignment. -/
def gen (written : Var) (label : Label) : DefSet :=
  fun name origin => name = written ∧ origin = some label

/-- The book's `kill` followed by `gen` equation for `[x := a]ˡ`. -/
def assign (definitions : DefSet) (written : Var) (label : Label) : DefSet :=
  union (kill written definitions) (gen written label)

end DefSet

/-- For one concrete execution, remember the most recent writer of each variable. -/
abbrev LastWriter := Var → Origin

namespace LastWriter

def entry : LastWriter := fun _ => none

def write (last : LastWriter) (written : Var) (label : Label) : LastWriter :=
  fun name => if name = written then some label else last name

end LastWriter

/-- Every concrete last writer is admitted by the approximate information. -/
def Covers (definitions : DefSet) (last : LastWriter) : Prop :=
  ∀ name, definitions name (last name)

/-- The entry facts cover the concrete state before any assignment runs. -/
theorem entry_covers : Covers DefSet.entry LastWriter.entry :=
  fun _ => rfl

/--
The assignment equation is locally sound. The proof is an ordinary term:
written variables take the generated branch; every other variable takes the
preserved branch. `Eq.mpr` exposes the only rewriting step, from the result of
`LastWriter.write` to the corresponding branch value.
-/
theorem assign_sound
    (definitions : DefSet)
    (last : LastWriter)
    (covered : Covers definitions last)
    (written : Var)
    (label : Label) :
    Covers (DefSet.assign definitions written label)
      (LastWriter.write last written label) :=
  fun name =>
    if same : name = written then
      Eq.mpr
        (congrArg
          (fun origin => DefSet.assign definitions written label name origin)
          (if_pos same))
        (Or.inr ⟨same, rfl⟩)
    else
      Eq.mpr
        (congrArg
          (fun origin => DefSet.assign definitions written label name origin)
          (if_neg same))
        (Or.inl ⟨same, covered name⟩)

/-- A generated definition is always present after its own assignment. -/
theorem generated_present
    (definitions : DefSet) (written : Var) (label : Label) :
    DefSet.assign definitions written label written (some label) :=
  Or.inr ⟨rfl, rfl⟩

/-- A definition of another variable survives an assignment. -/
theorem other_preserved
    (definitions : DefSet)
    (written other : Var)
    (label : Label)
    (origin : Origin)
    (different : other ≠ written)
    (present : definitions other origin) :
    DefSet.assign definitions written label other origin :=
  Or.inl ⟨different, present⟩

end PPA.Chapter01.ReachingDefinitions
