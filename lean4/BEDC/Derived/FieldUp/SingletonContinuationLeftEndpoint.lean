import BEDC.Derived.FieldUp.SingletonContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FieldSingletonCarrier_continuation_left_endpoint_iff {P Q R : BHist} :
    FieldSingletonCarrier Q -> Cont P Q R ->
      (FieldSingletonCarrier R <-> FieldSingletonCarrier P) := by
  intro carrierQ continuation
  constructor
  · intro carrierR
    cases carrierQ
    have sameRP : hsame R P := cont_deterministic continuation (cont_right_unit P)
    exact hsame_trans (hsame_symm sameRP) carrierR
  · intro carrierP
    exact FieldSingletonCarrier_continuation_closed carrierP carrierQ continuation

theorem fieldSingletonEmptyNonZero_continuation_left_endpoint_cancel_iff {P Q R : BHist} :
    fieldSingletonEmptyCarrier Q -> Cont P Q R ->
      (fieldSingletonEmptyNonZero R ↔ fieldSingletonEmptyNonZero P) := by
  intro carrierQ continuation
  constructor
  · intro nonzeroR classifiedP
    apply nonzeroR
    have carrierR : fieldSingletonEmptyCarrier R :=
      hsame_trans continuation (append_eq_empty_iff.mpr (And.intro classifiedP.left carrierQ))
    exact And.intro carrierR (And.intro (hsame_refl BHist.Empty) carrierR)
  · intro nonzeroP classifiedR
    apply nonzeroP
    have appendEmpty : hsame (append P Q) BHist.Empty :=
      hsame_trans (hsame_symm continuation) classifiedR.left
    have split := append_eq_empty_iff.mp appendEmpty
    exact And.intro split.left (And.intro (hsame_refl BHist.Empty) split.left)

end BEDC.Derived.FieldUp
