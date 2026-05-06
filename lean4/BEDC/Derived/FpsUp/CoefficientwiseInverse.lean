import BEDC.Derived.FpsUp.PointwiseAdditiveMonoid

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def FpsSingletonCoeffwiseInverse (_F : BHist) : BHist :=
  BHist.Empty

theorem FpsSingletonCoeffwiseInverse_zero_laws {F N n : BHist} :
    FpsSingletonCarrier F ->
      FpsSingletonClassifier N FpsSingletonZero ->
        FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F N n) FpsSingletonZero ∧
          FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff N F n) FpsSingletonZero ∧
            Cont (FpsSingletonPointwiseAdditionCoeff F N n)
              (FpsSingletonPointwiseAdditionCoeff N F n) BHist.Empty := by
  intro carrierF classifierN
  have coeffF :
      hsame (FpsSingletonCoeff F n) BHist.Empty :=
    (FpsSingletonCoeff_empty_ledger (F := F) (n := n) carrierF).left
  have coeffN :
      hsame (FpsSingletonCoeff N n) BHist.Empty :=
    (FpsSingletonCoeff_empty_ledger (F := N) (n := n) classifierN.left).left
  have leftEmpty :
      hsame (FpsSingletonPointwiseAdditionCoeff F N n) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro coeffF coeffN)
  have rightEmpty :
      hsame (FpsSingletonPointwiseAdditionCoeff N F n) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro coeffN coeffF)
  have zeroCarrier : FpsSingletonCarrier FpsSingletonZero :=
    hsame_refl BHist.Empty
  have leftClassifier :
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F N n) FpsSingletonZero :=
    And.intro leftEmpty
      (And.intro zeroCarrier (hsame_trans leftEmpty (hsame_symm zeroCarrier)))
  have rightClassifier :
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff N F n) FpsSingletonZero :=
    And.intro rightEmpty
      (And.intro zeroCarrier (hsame_trans rightEmpty (hsame_symm zeroCarrier)))
  exact And.intro leftClassifier
    (And.intro rightClassifier
      (by
        cases leftEmpty
        cases rightEmpty
        exact cont_right_unit BHist.Empty))

end BEDC.Derived.FpsUp
