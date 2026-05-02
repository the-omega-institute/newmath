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

end BEDC.Derived.FieldUp
