import PPA.Chapter01.ReachingDefinitions

/-!
The concrete abstraction/concretisation pair from PPA Section 1.5,
pp. 67--69.

A concrete point is a trace of definitions. `semanticReaching` keeps the last
definition of each variable in one trace. `abstract` unions those last-writer
facts over a set of traces; `concretize` selects exactly the traces whose
last-writer facts are admitted by an abstract reaching-definitions set.
-/

namespace PPA.Chapter01.AbstractInterpretation

open PPA.Chapter01
open PPA.Chapter01.ReachingDefinitions

abbrev Trace := List Definition
abbrev TraceSet := Trace → Prop

namespace Trace

def record (last : LastWriter) (definition : Definition) : LastWriter :=
  fun queried =>
    if queried = definition.name then definition.origin else last queried

def lastWriters (trace : Trace) : LastWriter :=
  trace.foldl record LastWriter.entry

/-- `SRD(trace)` on slide 68. -/
def semanticReaching (trace : Trace) : DefSet :=
  fun name origin => lastWriters trace name = origin

end Trace

namespace TraceSet

def Subset (lower upper : TraceSet) : Prop :=
  ∀ trace, lower trace → upper trace

end TraceSet

namespace DefSet

def Subset (lower upper : DefSet) : Prop :=
  ∀ name origin, lower name origin → upper name origin

end DefSet

/-- `α`: collect every last-writer fact exhibited by one concrete trace. -/
def abstract (traces : TraceSet) : DefSet :=
  fun name origin =>
    ∃ trace, traces trace ∧ Trace.semanticReaching trace name origin

/-- `γ`: retain traces whose last-writer facts are all admitted by `facts`. -/
def concretize (facts : DefSet) : TraceSet :=
  fun trace => DefSet.Subset (Trace.semanticReaching trace) facts

/-- The adjunction law printed on slides 67 and 69. -/
theorem reaching_galois (traces : TraceSet) (facts : DefSet) :
    TraceSet.Subset traces (concretize facts) ↔
      DefSet.Subset (abstract traces) facts :=
  ⟨fun concreteIncluded name origin witnessed =>
      match witnessed with
      | ⟨trace, present, reaches⟩ =>
          concreteIncluded trace present name origin reaches,
    fun abstractIncluded trace present name origin reaches =>
      abstractIncluded name origin ⟨trace, present, reaches⟩⟩

/-- Every concrete trace is admitted by the abstraction built from it. -/
theorem abstraction_is_sound (traces : TraceSet) :
    TraceSet.Subset traces (concretize (abstract traces)) :=
  (reaching_galois traces (abstract traces)).mpr
    (fun _ _ present => present)

/-- Abstracting the concretization cannot invent a fact outside its input. -/
theorem concretization_is_precise (facts : DefSet) :
    DefSet.Subset (abstract (concretize facts)) facts :=
  (reaching_galois (concretize facts) facts).mp
    (fun _ present => present)

/-! The two traces pictured on slide 68. -/
def shortTrace : Trace := [
  { name := .x, origin := none },
  { name := .y, origin := none },
  { name := .z, origin := none },
  { name := .y, origin := some 1 },
  { name := .z, origin := some 2 }
]

def loopTrace : Trace := shortTrace ++ [
  { name := .z, origin := some 4 },
  { name := .y, origin := some 5 }
]

def picturedTraces : TraceSet :=
  fun trace => trace = shortTrace ∨ trace = loopTrace

theorem pictured_abstraction_contains_x_entry :
    abstract picturedTraces .x none :=
  ⟨shortTrace, Or.inl rfl, rfl⟩

theorem pictured_abstraction_contains_y1 :
    abstract picturedTraces .y (some 1) :=
  ⟨shortTrace, Or.inl rfl, rfl⟩

theorem pictured_abstraction_contains_y5 :
    abstract picturedTraces .y (some 5) :=
  ⟨loopTrace, Or.inr rfl, rfl⟩

theorem pictured_abstraction_contains_z2 :
    abstract picturedTraces .z (some 2) :=
  ⟨shortTrace, Or.inl rfl, rfl⟩

theorem pictured_abstraction_contains_z4 :
    abstract picturedTraces .z (some 4) :=
  ⟨loopTrace, Or.inr rfl, rfl⟩

end PPA.Chapter01.AbstractInterpretation
