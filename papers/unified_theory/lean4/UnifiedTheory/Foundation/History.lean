import UnifiedTheory.Foundation.Mark

namespace UnifiedTheory

inductive MarkHist where
  | empty : MarkHist
  | ext (tag : Mark) (prev : MarkHist) : MarkHist
deriving DecidableEq, Repr

namespace MarkHist

def length : MarkHist -> Nat
  | empty => 0
  | ext _ prev => length prev + 1

def append : MarkHist -> MarkHist -> MarkHist
  | empty, h => h
  | ext tag prev, h => ext tag (append prev h)

theorem empty_append (h : MarkHist) : append empty h = h := rfl

theorem append_empty (h : MarkHist) : append h empty = h := by
  induction h with
  | empty => rfl
  | ext tag prev ih =>
      simp [append, ih]

theorem append_assoc (a b c : MarkHist) :
    append (append a b) c = append a (append b c) := by
  induction a with
  | empty => rfl
  | ext tag prev ih =>
      simp [append, ih]

theorem length_append (a b : MarkHist) :
    length (append a b) = length a + length b := by
  induction a with
  | empty => simp [append, length]
  | ext tag prev ih =>
      simp only [append, length, ih]
      omega

end MarkHist

structure Event (Op Arg : Type u) where
  src : MarkHist
  op : Op
  arg : Arg
  tag : Mark

abbrev EventHist (Op Arg : Type u) := List (Event Op Arg)

namespace EventHist

def generate {Op Arg : Type u}
    (h : EventHist Op Arg) (u : Event Op Arg) : EventHist Op Arg :=
  h ++ [u]

theorem generate_length {Op Arg : Type u}
    (h : EventHist Op Arg) (u : Event Op Arg) :
    (generate h u).length = h.length + 1 := by
  simp [generate]

end EventHist
end UnifiedTheory
