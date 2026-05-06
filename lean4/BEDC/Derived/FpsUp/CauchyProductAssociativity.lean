import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonCauchyProduct_assoc_classifier {F G H : BHist} :
    FpsSingletonClassifier (FpsSingletonMul (FpsSingletonMul F G) H)
        (FpsSingletonMul F (FpsSingletonMul G H)) ∧
      hsame (append (FpsSingletonMul (FpsSingletonMul F G) H) BHist.Empty)
        (append (FpsSingletonMul F (FpsSingletonMul G H)) BHist.Empty) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact ⟨⟨emptyCarrier, ⟨emptyCarrier, hsame_refl BHist.Empty⟩⟩,
    hsame_refl BHist.Empty⟩

end BEDC.Derived.FpsUp
