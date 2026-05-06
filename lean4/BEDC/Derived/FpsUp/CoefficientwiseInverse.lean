import BEDC.Derived.FpsUp.PointwiseAdditiveMonoid

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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

theorem FpsSingletonPointwiseAdditiveGroup_laws :
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
          FpsSingletonClassifier (FpsSingletonAdd F FpsSingletonZero) F) ∧
      (forall {F N n : BHist}, FpsSingletonCarrier F ->
        FpsSingletonClassifier N FpsSingletonZero ->
          FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F N n)
              FpsSingletonZero ∧
            FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff N F n)
              FpsSingletonZero ∧
              Cont (FpsSingletonPointwiseAdditionCoeff F N n)
                (FpsSingletonPointwiseAdditionCoeff N F n) BHist.Empty) ∧
      (forall {F : BHist}, FpsSingletonCarrier F ->
        exists N : BHist,
          FpsSingletonClassifier N FpsSingletonZero ∧
            forall n : BHist,
              FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F N n)
                FpsSingletonZero ∧
                FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff N F n)
                  FpsSingletonZero) := by
  have monoid := FpsSingletonPointwiseAdditiveMonoid_laws
  cases monoid with
  | intro zeroSame rest =>
      cases rest with
      | intro zeroCarrier rest =>
          cases rest with
          | intro addClosed rest =>
              cases rest with
              | intro addTransport rest =>
                  cases rest with
                  | intro addAssoc addIdentity =>
                      constructor
                      · exact zeroSame
                      · constructor
                        · exact zeroCarrier
                        · constructor
                          · exact addClosed
                          · constructor
                            · exact addTransport
                            · constructor
                              · exact addAssoc
                              · constructor
                                · exact addIdentity
                                · constructor
                                  · intro F N n carrierF classifierN
                                    exact
                                      FpsSingletonCoeffwiseInverse_zero_laws
                                        (F := F) (N := N) (n := n)
                                        carrierF classifierN
                                  · intro F carrierF
                                    refine Exists.intro FpsSingletonZero ?_
                                    constructor
                                    · exact And.intro zeroCarrier
                                        (And.intro zeroCarrier (hsame_refl FpsSingletonZero))
                                    · intro n
                                      have inverseRows :=
                                        FpsSingletonCoeffwiseInverse_zero_laws
                                          (F := F) (N := FpsSingletonZero) (n := n)
                                          carrierF
                                          (And.intro zeroCarrier
                                            (And.intro zeroCarrier
                                              (hsame_refl FpsSingletonZero)))
                                      exact And.intro inverseRows.left inverseRows.right.left

end BEDC.Derived.FpsUp
