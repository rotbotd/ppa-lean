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

def extend (trace : Trace) (written : Var) (label : Label) : Trace :=
  trace ++ [{ name := written, origin := some label }]

theorem lastWriters_extend (trace : Trace) (written : Var) (label : Label) :
    lastWriters (extend trace written label) =
      record (lastWriters trace) { name := written, origin := some label } :=
  Eq.trans List.foldl_append rfl

/-- Appending one concrete write induces exactly the kill/gen transfer. -/
theorem semanticReaching_extend
    (trace : Trace) (written : Var) (label : Label) :
    semanticReaching (extend trace written label) =
      DefSet.assign (semanticReaching trace) written label :=
  funext fun name =>
    funext fun origin =>
      propext
        (show
          lastWriters (extend trace written label) name = origin ↔
            DefSet.assign (semanticReaching trace) written label name origin
        from
          let writerAt :=
            congrArg (fun writers => writers name)
              (lastWriters_extend trace written label)
          if same : name = written then
            ⟨fun reaches =>
                Or.inr
                  ⟨same,
                    (calc
                      some label =
                          (if name = written then some label
                            else lastWriters trace name) := (if_pos same).symm
                      _ = lastWriters (extend trace written label) name :=
                        writerAt.symm
                      _ = origin := reaches).symm⟩,
              fun valid =>
                match valid with
                | Or.inl preserved => False.elim (preserved.1 same)
                | Or.inr generated =>
                    calc
                      lastWriters (extend trace written label) name =
                          (if name = written then some label
                            else lastWriters trace name) := writerAt
                      _ = some label := if_pos same
                      _ = origin := generated.2.symm⟩
          else
            ⟨fun reaches =>
                Or.inl
                  ⟨same,
                    calc
                      lastWriters trace name =
                          (if name = written then some label
                            else lastWriters trace name) := (if_neg same).symm
                      _ = lastWriters (extend trace written label) name :=
                        writerAt.symm
                      _ = origin := reaches⟩,
              fun valid =>
                match valid with
                | Or.inl preserved =>
                    calc
                      lastWriters (extend trace written label) name =
                          (if name = written then some label
                            else lastWriters trace name) := writerAt
                      _ = lastWriters trace name := if_neg same
                      _ = origin := preserved.2
                | Or.inr generated => False.elim (same generated.1)⟩)

end Trace

namespace TraceSet

def Subset (lower upper : TraceSet) : Prop :=
  ∀ trace, lower trace → upper trace

end TraceSet

namespace DefSet

def Subset (lower upper : DefSet) : Prop :=
  ∀ name origin, lower name origin → upper name origin

theorem assign_monotone
    {lower upper : DefSet}
    (included : Subset lower upper)
    (written : Var) (label : Label) :
    Subset
      (ReachingDefinitions.DefSet.assign lower written label)
      (ReachingDefinitions.DefSet.assign upper written label) :=
  fun name origin valid =>
    match valid with
    | Or.inl preserved =>
        Or.inl ⟨preserved.1, included name origin preserved.2⟩
    | Or.inr generated => Or.inr generated

end DefSet

/-- `α`: collect every last-writer fact exhibited by one concrete trace. -/
def abstract (traces : TraceSet) : DefSet :=
  fun name origin =>
    ∃ trace, traces trace ∧ Trace.semanticReaching trace name origin

/-- `γ`: retain traces whose last-writer facts are all admitted by `facts`. -/
def concretize (facts : DefSet) : TraceSet :=
  fun trace => DefSet.Subset (Trace.semanticReaching trace) facts

def concreteAssign
    (traces : TraceSet) (written : Var) (label : Label) : TraceSet :=
  fun output =>
    ∃ input, traces input ∧ output = Trace.extend input written label

/-- The transfer obtained by crossing to traces, appending, and returning. -/
def inducedAssign (facts : DefSet) (written : Var) (label : Label) : DefSet :=
  abstract (concreteAssign (concretize facts) written label)

def ConcretelyClosed (facts : DefSet) : Prop :=
  abstract (concretize facts) = facts

def ConcretelyInhabited (facts : DefSet) : Prop :=
  ∃ trace, concretize facts trace

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

/-- The induced concrete transfer never exceeds the kill/gen transfer. -/
theorem inducedAssign_sound
    (facts : DefSet) (written : Var) (label : Label) :
    DefSet.Subset
      (inducedAssign facts written label)
      (ReachingDefinitions.DefSet.assign facts written label) :=
  fun name origin witnessed =>
    match witnessed with
    | ⟨_, ⟨input, inputAllowed, rfl⟩, reaches⟩ =>
        let atFact :
            Trace.semanticReaching (Trace.extend input written label)
                name origin =
              ReachingDefinitions.DefSet.assign
                (Trace.semanticReaching input) written label name origin :=
          congrArg (fun definitions => definitions name origin)
            (Trace.semanticReaching_extend input written label)
        DefSet.assign_monotone inputAllowed written label name origin
          (transport {
            Trace.semanticReaching (Trace.extend input written label)
                name origin ->
            ReachingDefinitions.DefSet.assign
                (Trace.semanticReaching input) written label name origin
          } atFact reaches)

/-- Closed, inhabited abstract states lose nothing through concretization. -/
theorem inducedAssign_complete
    (facts : DefSet) (written : Var) (label : Label)
    (closed : ConcretelyClosed facts)
    (inhabited : ConcretelyInhabited facts) :
    DefSet.Subset
      (ReachingDefinitions.DefSet.assign facts written label)
      (inducedAssign facts written label) :=
  fun name origin valid =>
    match valid with
    | Or.inl preserved =>
        let closedAt :
            abstract (concretize facts) name origin = facts name origin :=
          congrArg (fun definitions => definitions name origin) closed
        let reified : abstract (concretize facts) name origin :=
          transport {
            facts name origin ->
            abstract (concretize facts) name origin
          } closedAt.symm preserved.2
        match reified with
        | ⟨input, inputAllowed, reachesInput⟩ =>
            let semanticAt :
                Trace.semanticReaching (Trace.extend input written label)
                    name origin =
                  ReachingDefinitions.DefSet.assign
                    (Trace.semanticReaching input) written label name origin :=
              congrArg (fun definitions => definitions name origin)
                (Trace.semanticReaching_extend input written label)
            ⟨Trace.extend input written label,
              ⟨input, inputAllowed, rfl⟩,
              transport {
                ReachingDefinitions.DefSet.assign
                    (Trace.semanticReaching input) written label name origin ->
                Trace.semanticReaching (Trace.extend input written label)
                    name origin
              } semanticAt.symm (Or.inl ⟨preserved.1, reachesInput⟩)⟩
    | Or.inr generated =>
        match inhabited with
        | ⟨input, inputAllowed⟩ =>
            let semanticAt :
                Trace.semanticReaching (Trace.extend input written label)
                    name origin =
                  ReachingDefinitions.DefSet.assign
                    (Trace.semanticReaching input) written label name origin :=
              congrArg (fun definitions => definitions name origin)
                (Trace.semanticReaching_extend input written label)
            ⟨Trace.extend input written label,
              ⟨input, inputAllowed, rfl⟩,
              transport {
                ReachingDefinitions.DefSet.assign
                    (Trace.semanticReaching input) written label name origin ->
                Trace.semanticReaching (Trace.extend input written label)
                    name origin
              } semanticAt.symm (Or.inr generated)⟩

/-- Under the slide's `α ∘ γ = id` hypothesis, induction yields kill/gen. -/
theorem inducedAssign_eq_assign
    (facts : DefSet) (written : Var) (label : Label)
    (closed : ConcretelyClosed facts)
    (inhabited : ConcretelyInhabited facts) :
    inducedAssign facts written label =
      ReachingDefinitions.DefSet.assign facts written label :=
  funext fun name =>
    funext fun origin =>
      propext
        ⟨inducedAssign_sound facts written label name origin,
          inducedAssign_complete facts written label closed inhabited
            name origin⟩

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
