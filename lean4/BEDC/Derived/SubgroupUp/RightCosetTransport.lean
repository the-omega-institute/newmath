import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

theorem SubgroupCentralizerRightCosetClassifier_hsame_transport
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x x' y y' : BHist} :
    SubgroupCentralizerRightCosetClassifier mul inv a x y -> hsame x x' -> hsame y y' ->
      SubgroupCentralizerRightCosetClassifier mul inv a x' y' := by
  intro classified sameXX' sameYY'
  have kernel : SubgroupCentralizerQuotientKernel mul inv a x y :=
    (SubgroupCentralizerRightCosetClassifier_quotientKernel_iff
      assocC leftId mulCongr leftInv rightInv).mp classified
  have transported : SubgroupCentralizerQuotientKernel mul inv a x' y' :=
    SubgroupCentralizerQuotientKernel_hsame_transport
      assocC leftId rightId mulCongr leftInv rightInv kernel sameXX' sameYY'
  exact (SubgroupCentralizerRightCosetClassifier_quotientKernel_iff
    assocC leftId mulCongr leftInv rightInv).mpr transported

protected theorem SubgroupCentralizerRightCosetClassifier_trans_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y z : BHist} :
    SubgroupCentralizerRightCosetClassifier mul inv a x y ->
      SubgroupCentralizerRightCosetClassifier mul inv a y z ->
        SubgroupCentralizerRightCosetClassifier mul inv a x z := by
  intro classifiedXY classifiedYZ
  cases classifiedXY.right.right with
  | intro u witnessU =>
      cases classifiedYZ.right.right with
      | intro v witnessV =>
          have centralUV : SubgroupCentralizerCarrier mul a (mul u v) :=
            BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
              assocC rightId mulCongr witnessU.left witnessV.left
          have sameZ : hsame z (mul x (mul u v)) := by
            exact hsame_trans witnessV.right
              (hsame_trans (mulCongr witnessU.right (hsame_refl v)) (assocC x u v))
          exact And.intro classifiedXY.left
            (And.intro classifiedYZ.right.left (Exists.intro (mul u v)
              (And.intro centralUV sameZ)))

end BEDC.Derived.SubgroupUp
