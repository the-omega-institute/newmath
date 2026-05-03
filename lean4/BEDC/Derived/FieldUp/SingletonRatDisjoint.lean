import BEDC.Derived.FieldUp.SingletonEmpty
import BEDC.Derived.RatUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem fieldSingletonEmptyCarrier_RatHistoryCarrier_disjoint_certificate :
    SemanticNameCert fieldSingletonEmptyCarrier fieldSingletonEmptyCarrier
      fieldSingletonEmptyCarrier fieldSingletonEmptyClassifier ∧
      (∀ {h : BHist}, fieldSingletonEmptyCarrier h -> RatHistoryCarrier h -> False) := by
  constructor
  · exact fieldSingletonEmptyCarrier_semanticNameCert
  · intro h singletonCarrier ratCarrier
    exact RatHistoryCarrier_not_empty ratCarrier singletonCarrier

end BEDC.Derived.FieldUp
