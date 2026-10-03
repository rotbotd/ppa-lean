/-!
The labelled `WHILE` language used throughout PPA Chapter 1.

Labels belong to elementary blocks: assignments, skips, guards, and loop
conditions. A relational semantics leaves divergence visible instead of hiding
it behind a fuel parameter.
-/

namespace PPA.Chapter01

abbrev Label := Nat

inductive Var where
  | x | y | z
  deriving BEq, DecidableEq, Repr, ReflBEq, LawfulBEq

inductive AOp where
  | add | sub | mul
  deriving DecidableEq, Repr

inductive ROp where
  | eq | lt | le
  deriving DecidableEq, Repr

inductive AExp where
  | var (name : Var)
  | int (value : Int)
  | bin (op : AOp) (left right : AExp)
  deriving DecidableEq, Repr

inductive BExp where
  | true
  | false
  | not (body : BExp)
  | and (left right : BExp)
  | rel (op : ROp) (left right : AExp)
  deriving DecidableEq, Repr

inductive Stmt where
  | assign (label : Label) (name : Var) (value : AExp)
  | skip (label : Label)
  | seq (first second : Stmt)
  | ite (label : Label) (guard : BExp) (yes no : Stmt)
  | while (label : Label) (guard : BExp) (body : Stmt)
  deriving DecidableEq, Repr

abbrev State := Var → Int

namespace State

def write (state : State) (name : Var) (value : Int) : State :=
  fun queried => if queried = name then value else state queried

end State

namespace AExp

def eval : AExp → State → Int
  | .var name, state => state name
  | .int value, _ => value
  | .bin .add left right, state => eval left state + eval right state
  | .bin .sub left right, state => eval left state - eval right state
  | .bin .mul left right, state => eval left state * eval right state

end AExp

namespace BExp

def eval : BExp → State → Bool
  | .true, _ => Bool.true
  | .false, _ => Bool.false
  | .not body, state => !(eval body state)
  | .and left right, state => eval left state && eval right state
  | .rel .eq left right, state => AExp.eval left state == AExp.eval right state
  | .rel .lt left right, state => AExp.eval left state < AExp.eval right state
  | .rel .le left right, state => AExp.eval left state ≤ AExp.eval right state

end BExp

inductive BigStep : Stmt → State → State → Prop where
  | assign : BigStep (.assign label name value) state
      (state.write name (value.eval state))
  | skip : BigStep (.skip label) state state
  | seq : BigStep first before middle → BigStep second middle after →
      BigStep (.seq first second) before after
  | iteTrue : BExp.eval condition before = Bool.true →
      BigStep yes before after →
      BigStep (.ite label condition yes no) before after
  | iteFalse : BExp.eval condition before = Bool.false →
      BigStep no before after →
      BigStep (.ite label condition yes no) before after
  | whileFalse : BExp.eval condition before = Bool.false →
      BigStep (.while label condition body) before before
  | whileTrue : BExp.eval condition before = Bool.true →
      BigStep body before middle →
      BigStep (.while label condition body) middle after →
      BigStep (.while label condition body) before after

/-- PPA Section 1.3's six-label running program. -/
def reachingExample : Stmt :=
  .seq (.assign 1 .y (.var .x))
    (.seq (.assign 2 .z (.int 1))
      (.seq
        (.while 3 (.rel .lt (.int 0) (.var .y))
          (.seq (.assign 4 .z (.bin .mul (.var .z) (.var .y)))
            (.assign 5 .y (.bin .sub (.var .y) (.int 1)))))
        (.assign 6 .y (.int 0))))

end PPA.Chapter01
