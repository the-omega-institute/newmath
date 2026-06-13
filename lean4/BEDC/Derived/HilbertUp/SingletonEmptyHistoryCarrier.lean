import BEDC.Derived.HilbertUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.NormUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist

theorem HilbertSingletonEmptyHistoryCarrier_admission :
    VecSpaceSingletonCarrier BHist.Empty ∧
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct BHist.Empty BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        RealConstantHistoryClassifier (NormSingletonNorm BHist.Empty)
          (BHist.e1 (BHist.e1 BHist.Empty)) ∧
          hsame BHist.Empty BHist.Empty := by
  -- BEDC touchpoint anchor: BHist hsame RealConstantHistoryClassifier VecSpaceSingletonCarrier
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : VecSpaceSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  have compatibility := HilbertSingleton_inner_product_norm_compatibility emptyCarrier
  have innerZero :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct BHist.Empty BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr compatibility.right emptyClassified
  have normZero :
      RealConstantHistoryClassifier (NormSingletonNorm BHist.Empty)
        (BHist.e1 (BHist.e1 BHist.Empty)) :=
    Iff.mpr (NormSingletonEmptyHistory_zero_exactness emptyCarrier) emptyClassified
  exact And.intro emptyCarrier (And.intro innerZero (And.intro normZero (hsame_refl BHist.Empty)))

end BEDC.Derived.HilbertUp
