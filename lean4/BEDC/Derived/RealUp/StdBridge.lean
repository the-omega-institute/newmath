import BEDC.Derived.RealUp.SemanticCertificate

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem RealUp_StdBridge {d e : BHist} :
    RatHistoryClassifier d e ->
      RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) ∧
        SemanticNameCert RealConstantHistoryCarrier RealConstantHistoryCarrier
          RealConstantHistoryCarrier RealConstantHistoryClassifier := by
  intro ratClassifier
  exact And.intro
    (RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier)
    RealConstantHistory_semanticNameCert

end BEDC.Derived.RealUp
