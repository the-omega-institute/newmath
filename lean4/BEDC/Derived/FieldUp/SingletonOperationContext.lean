import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem fieldSingletonEmptyClassifier_append_endpoint_iff {L R endpoint out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R)
    (hEndpoint : fieldSingletonEmptyCarrier endpoint) :
    fieldSingletonEmptyClassifier (append L endpoint) (append R out) ↔
      fieldSingletonEmptyCarrier out := by
  constructor
  · intro classified
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact rightSplit.right
  · intro outCarrier
    have leftCarrier : fieldSingletonEmptyCarrier (append L endpoint) :=
      append_eq_empty_iff.mpr (And.intro hL hEndpoint)
    have rightCarrier : fieldSingletonEmptyCarrier (append R out) :=
      append_eq_empty_iff.mpr (And.intro hR outCarrier)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem fieldSingletonEmpty_operation_context_normalization {L R h k out : BHist}
    (hL : fieldSingletonEmptyCarrier L) (hR : fieldSingletonEmptyCarrier R) :
    (fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyMul h k)) (append R out) ↔
      fieldSingletonEmptyCarrier out) ∧
    (fieldSingletonEmptyClassifier (append L fieldSingletonEmptyOne) (append R out) ↔
      fieldSingletonEmptyCarrier out) ∧
    (∀ (p : fieldSingletonEmptyNonZero h),
      fieldSingletonEmptyClassifier (append L (fieldSingletonEmptyInv h p)) (append R out) ↔
        fieldSingletonEmptyCarrier out) := by
  constructor
  · exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)
  · constructor
    · exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)
    · intro p
      exact fieldSingletonEmptyClassifier_append_endpoint_iff hL hR (hsame_refl BHist.Empty)

end BEDC.Derived.FieldUp
