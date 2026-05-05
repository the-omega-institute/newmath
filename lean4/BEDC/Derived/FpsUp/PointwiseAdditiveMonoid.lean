import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist

private theorem FpsSingletonEmpty_classified :
    FpsSingletonClassifier BHist.Empty BHist.Empty := by
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem FpsSingletonPointwiseAdditiveMonoid_laws :
    hsame FpsSingletonZero BHist.Empty ∧
      FpsSingletonCarrier FpsSingletonZero ∧
      (forall {F G : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier (FpsSingletonAdd F G)) ∧
      (forall {F G F' G' : BHist}, FpsSingletonClassifier F F' ->
        FpsSingletonClassifier G G' ->
          FpsSingletonClassifier (FpsSingletonAdd F G) (FpsSingletonAdd F' G')) ∧
      (forall {F G H : BHist}, FpsSingletonCarrier F -> FpsSingletonCarrier G ->
        FpsSingletonCarrier H ->
          FpsSingletonClassifier (FpsSingletonAdd (FpsSingletonAdd F G) H)
            (FpsSingletonAdd F (FpsSingletonAdd G H))) ∧
      (forall {F : BHist}, FpsSingletonCarrier F ->
        FpsSingletonClassifier (FpsSingletonAdd FpsSingletonZero F) F ∧
          FpsSingletonClassifier (FpsSingletonAdd F FpsSingletonZero) F) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · intro F G carrierF carrierG
        exact hsame_refl BHist.Empty
      · constructor
        · intro F G F' G' sameF sameG
          exact FpsSingletonEmpty_classified
        · constructor
          · intro F G H carrierF carrierG carrierH
            exact FpsSingletonEmpty_classified
          · intro F carrierF
            constructor
            · exact And.intro (hsame_refl BHist.Empty)
                (And.intro carrierF (hsame_symm carrierF))
            · exact And.intro (hsame_refl BHist.Empty)
                (And.intro carrierF (hsame_symm carrierF))

end BEDC.Derived.FpsUp
