import BEDC.Derived.NormUp
import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.NormUp
open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def HilbertSingletonInnerProduct (_m _n : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem HilbertSingleton_inner_product_norm_compatibility {m : BHist} :
    VecSpaceSingletonCarrier m ->
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) ∧
        (RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m)
          (BHist.e1 (BHist.e1 BHist.Empty)) ↔ VecSpaceSingletonClassifier m BHist.Empty) := by
  intro carrierM
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (HilbertSingletonInnerProduct m m) (NormSingletonNorm m) :=
    RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro realClassifier (NormSingletonEmptyHistory_zero_exactness carrierM)

end BEDC.Derived.HilbertUp
