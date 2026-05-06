import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CommRingSingletonClassifier_continuation_empty_result_iff {P Q R : BHist} :
    Cont P Q R -> (CommRingSingletonClassifier P Q <-> hsame R BHist.Empty) := by
  intro continuation
  constructor
  · intro classified
    cases continuation
    exact append_eq_empty_iff.mpr (And.intro classified.left classified.right.left)
  · intro resultEmpty
    cases continuation
    have endpoints := append_eq_empty_iff.mp resultEmpty
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem CommRingSingletonCarrier_continuation_split_iff {P Q R : BHist} :
    Cont P Q R ->
      (CommRingSingletonCarrier R ↔
        CommRingSingletonCarrier P ∧ CommRingSingletonCarrier Q) := by
  intro continuation
  constructor
  · intro resultCarrier
    cases continuation
    exact append_eq_empty_iff.mp resultCarrier
  · intro carriers
    cases continuation
    exact append_eq_empty_iff.mpr carriers

end BEDC.Derived.CommRingUp
