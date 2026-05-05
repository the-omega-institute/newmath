import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FpsSingletonPointwiseAdditionCoeff_zero_laws {F n : BHist} :
    FpsSingletonCarrier F ->
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F FpsSingletonZero n) F ∧
        FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff FpsSingletonZero F n) F ∧
          hsame (FpsSingletonPointwiseAdditionCoeff F FpsSingletonZero n) BHist.Empty ∧
            hsame (FpsSingletonPointwiseAdditionCoeff FpsSingletonZero F n) BHist.Empty := by
  intro carrierF
  have leftEmpty :
      hsame (FpsSingletonPointwiseAdditionCoeff F FpsSingletonZero n) BHist.Empty :=
    append_eq_empty_iff.mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have rightEmpty :
      hsame (FpsSingletonPointwiseAdditionCoeff FpsSingletonZero F n) BHist.Empty :=
    append_eq_empty_iff.mpr
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  have leftClassifier :
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F FpsSingletonZero n) F :=
    And.intro leftEmpty
      (And.intro carrierF (hsame_trans leftEmpty (hsame_symm carrierF)))
  have rightClassifier :
      FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff FpsSingletonZero F n) F :=
    And.intro rightEmpty
      (And.intro carrierF (hsame_trans rightEmpty (hsame_symm carrierF)))
  exact And.intro leftClassifier
    (And.intro rightClassifier (And.intro leftEmpty rightEmpty))

end BEDC.Derived.FpsUp
