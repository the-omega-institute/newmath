import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp

theorem QuotientGroupCentralizerNormalizer_abelian_terminal_projection_uniqueness
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y thetaX thetaY : BHist} :
    SubgroupCentralizerNormalizer mul inv a x ->
      SubgroupCentralizerNormalizer mul inv a y ->
        QuotientGroupSingletonCarrier thetaX ->
          QuotientGroupSingletonCarrier thetaY ->
            QuotientGroupSingletonClassifier thetaX BHist.Empty ∧
              QuotientGroupSingletonClassifier thetaY BHist.Empty ∧
                ((QuotientGroupSingletonClassifier thetaX thetaY <->
                    QuotientGroupSingletonClassifier BHist.Empty BHist.Empty) ∧
                  (QuotientGroupSingletonClassifier thetaX thetaY <->
                    SubgroupCentralizerQuotientKernel mul inv a x y)) := by
  intro normalizesX normalizesY carrierThetaX carrierThetaY
  have terminal :=
    QuotientGroupCentralizerNormalizer_abelian_terminal_projection
      assocC leftId rightId commC mulCongr leftInv rightInv normalizesX normalizesY
  have singletonEmpty : QuotientGroupSingletonClassifier BHist.Empty BHist.Empty :=
    terminal.right
  have thetaXEmpty : QuotientGroupSingletonClassifier thetaX BHist.Empty :=
    And.intro carrierThetaX
      (And.intro (hsame_refl BHist.Empty) carrierThetaX)
  have thetaYEmpty : QuotientGroupSingletonClassifier thetaY BHist.Empty :=
    And.intro carrierThetaY
      (And.intro (hsame_refl BHist.Empty) carrierThetaY)
  have thetaXY : QuotientGroupSingletonClassifier thetaX thetaY :=
    And.intro carrierThetaX
      (And.intro carrierThetaY
        (hsame_trans carrierThetaX (hsame_symm carrierThetaY)))
  have kernelXY : SubgroupCentralizerQuotientKernel mul inv a x y :=
    Iff.mpr terminal.left singletonEmpty
  exact And.intro thetaXEmpty
    (And.intro thetaYEmpty
      (And.intro
        (Iff.intro (fun _classified => singletonEmpty) (fun _classified => thetaXY))
        (Iff.intro (fun _classified => kernelXY) (fun _kernel => thetaXY))))

end BEDC.Derived.QuotientGroupUp
