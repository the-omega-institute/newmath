import BEDC.Derived.IntUp.HistorySemantic

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem IntHistoryClassifier_positive_append_context_iff {a m n : BHist} :
    UnaryHistory a -> UnaryHistory m -> UnaryHistory n ->
      (IntHistoryClassifier (BHist.e0 (append a m)) (BHist.e0 (append a n)) <->
        IntHistoryClassifier (BHist.e0 m) (BHist.e0 n)) ∧
      (IntHistoryClassifier (BHist.e1 (append a m)) (BHist.e1 (append a n)) <->
        IntHistoryClassifier (BHist.e1 m) (BHist.e1 n)) := by
  intro unaryA unaryM unaryN
  have unaryAM : UnaryHistory (append a m) :=
    unary_append_closed unaryA unaryM
  have unaryAN : UnaryHistory (append a n) :=
    unary_append_closed unaryA unaryN
  have appendReadback :=
    IntHistoryClassifier_same_tag_readback_iff (m := append a m) (n := append a n)
  have baseReadback := IntHistoryClassifier_same_tag_readback_iff (m := m) (n := n)
  constructor
  · constructor
    · intro classified
      have read := Iff.mp appendReadback.left classified
      have sameMN : hsame m n :=
        append_left_cancel (h := a) read.right.right
      exact Iff.mpr baseReadback.left (And.intro unaryM (And.intro unaryN sameMN))
    · intro classified
      have read := Iff.mp baseReadback.left classified
      have sameAppend : hsame (append a m) (append a n) :=
        congrArg (append a) read.right.right
      exact Iff.mpr appendReadback.left
        (And.intro unaryAM (And.intro unaryAN sameAppend))
  · constructor
    · intro classified
      have read := Iff.mp appendReadback.right classified
      have sameMN : hsame m n :=
        append_left_cancel (h := a) read.right.right
      exact Iff.mpr baseReadback.right (And.intro unaryM (And.intro unaryN sameMN))
    · intro classified
      have read := Iff.mp baseReadback.right classified
      have sameAppend : hsame (append a m) (append a n) :=
        congrArg (append a) read.right.right
      exact Iff.mpr appendReadback.right
        (And.intro unaryAM (And.intro unaryAN sameAppend))

end BEDC.Derived.IntUp
