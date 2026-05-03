import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonClassifier_append_suffix_cancel_iff {P R Q S : BHist} :
    FieldSingletonCarrier Q -> FieldSingletonCarrier S ->
      (FieldSingletonClassifier (append P Q) (append R S) ↔
        FieldSingletonClassifier P R) := by
  intro carrierQ carrierS
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.left
      (And.intro rightSplit.left (hsame_trans leftSplit.left (hsame_symm rightSplit.left)))
  · intro classified
    have leftCarrier : FieldSingletonCarrier (append P Q) :=
      append_eq_empty_iff.mpr (And.intro classified.left carrierQ)
    have rightCarrier : FieldSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro classified.right.left carrierS)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.FieldUp
