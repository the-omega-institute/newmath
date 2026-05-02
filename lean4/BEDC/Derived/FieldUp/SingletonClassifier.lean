import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem FieldSingletonClassifier_empty_endpoints_iff {h k : BHist} :
    FieldSingletonClassifier h k ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  constructor
  · intro same
    exact And.intro same.left same.right.left
  · intro endpoints
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem fieldSingletonEmptyNonZero_visible_headed {h : BHist} :
    fieldSingletonEmptyNonZero (BHist.e0 h) ∧
      fieldSingletonEmptyNonZero (BHist.e1 h) := by
  constructor
  · intro classified
    exact not_hsame_e0_empty classified.left
  · intro classified
    exact not_hsame_e1_empty classified.left

end BEDC.Derived.FieldUp
