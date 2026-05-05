import BEDC.Derived.RealUp.Core
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.NormUp

open BEDC.Derived.RatUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def NormSingletonNorm (_m : BHist) : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem NormSingletonEmptyHistory_carrier_classifier {m n : BHist} :
    VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
      RealConstantHistoryCarrier (NormSingletonNorm m) ∧
        VecSpaceSingletonClassifier m n ∧
          RealConstantHistoryClassifier (NormSingletonNorm m) (NormSingletonNorm n) ∧
            hsame (NormSingletonNorm m) (BHist.e1 (BHist.e1 BHist.Empty)) := by
  intro carrierM carrierN
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have ratCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr emptyUnary
  have realCarrier : RealConstantHistoryCarrier (NormSingletonNorm m) := by
    exact RealConstantHistoryCarrier_e1_iff_rat.mpr ratCarrier
  have vectorClassifier : VecSpaceSingletonClassifier m n :=
    And.intro carrierM (And.intro carrierN (hsame_trans carrierM (hsame_symm carrierN)))
  have ratClassifier :
      RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
    And.intro ratCarrier (And.intro ratCarrier (hsame_refl (BHist.e1 BHist.Empty)))
  have realClassifier :
      RealConstantHistoryClassifier (NormSingletonNorm m) (NormSingletonNorm n) := by
    exact RealConstantHistoryClassifier_e1_iff_rat.mpr ratClassifier
  exact And.intro realCarrier
    (And.intro vectorClassifier
      (And.intro realClassifier (hsame_refl (BHist.e1 (BHist.e1 BHist.Empty)))))

end BEDC.Derived.NormUp
