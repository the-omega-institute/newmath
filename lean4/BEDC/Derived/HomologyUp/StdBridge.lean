import BEDC.Derived.HomologyUp

namespace BEDC.Derived.HomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem HomologyUp_StdBridge :
    SemanticNameCert HomologySingletonCycleCarrier HomologySingletonCycleCarrier
      HomologySingletonCycleCarrier HomologySingletonCycleClassifier ∧
      HomologySingletonCycleCarrier BHist.Empty ∧
        HomologySingletonCycleClassifier BHist.Empty BHist.Empty := by
  exact And.intro HomologySingletonCycle_semanticNameCert
    (And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))))

end BEDC.Derived.HomologyUp
