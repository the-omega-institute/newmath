import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

private theorem FpsSingletonEmpty_classified :
    FpsSingletonClassifier BHist.Empty BHist.Empty := by
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

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

theorem FpsSingletonPointwiseAdditiveMonoid_laws :
    hsame FpsSingletonZero BHist.Empty ∧
      FpsSingletonCarrier FpsSingletonZero ∧
      (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier (FpsSingletonAdd F G) ∧
          FpsSingletonClassifier (FpsSingletonAdd F G) BHist.Empty) ∧
      (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
        FpsSingletonClassifier G G' ->
          FpsSingletonClassifier (FpsSingletonAdd F G) (FpsSingletonAdd F' G')) ∧
      (forall {F G H : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier H ->
          FpsSingletonClassifier
            (FpsSingletonAdd (FpsSingletonAdd F G) H)
            (FpsSingletonAdd F (FpsSingletonAdd G H))) ∧
      (forall {F : BHist}, FpsSingletonCarrier F ->
        FpsSingletonClassifier (FpsSingletonAdd FpsSingletonZero F) F ∧
          FpsSingletonClassifier (FpsSingletonAdd F FpsSingletonZero) F) := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : FpsSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · intro F G _carrierF _carrierG
        exact And.intro emptyCarrier emptyClassifier
      · constructor
        · intro F G F' G' _sameF _sameG
          exact emptyClassifier
        · constructor
          · intro F G H _carrierF _carrierG _carrierH
            exact emptyClassifier
          · intro F carrierF
            have zeroLeft : FpsSingletonClassifier BHist.Empty F :=
              And.intro emptyCarrier (And.intro carrierF (hsame_symm carrierF))
            exact And.intro zeroLeft zeroLeft

end BEDC.Derived.FpsUp
