import BEDC.Derived.FieldUp.SingletonAppend

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_append_pair_iff {h h' k k' : BHist} :
    FieldSingletonClassifier (append h k) (append h' k') <->
      FieldSingletonClassifier h h' /\ FieldSingletonClassifier k k' := by
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    have hh' : FieldSingletonClassifier h h' :=
      And.intro leftSplit.left
        (And.intro rightSplit.left
          (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
    have kk' : FieldSingletonClassifier k k' :=
      And.intro leftSplit.right
        (And.intro rightSplit.right
          (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
    exact And.intro hh' kk'
  · intro pairClassified
    have leftCarrier : FieldSingletonCarrier (append h k) :=
      append_eq_empty_iff.mpr (And.intro pairClassified.left.left pairClassified.right.left)
    have rightCarrier : FieldSingletonCarrier (append h' k') :=
      append_eq_empty_iff.mpr
        (And.intro pairClassified.left.right.left pairClassified.right.right.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.FieldUp
