import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerRightQuotientClassifier_trans_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y z : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y ->
      SubgroupCentralizerRightQuotientClassifier mul inv a y z ->
        SubgroupCentralizerRightQuotientClassifier mul inv a x z := by
  intro xy yz
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelYZ :
      SubgroupCentralizerRightQuotientClassifier mul inv a y z <->
        SubgroupCentralizerQuotientKernel mul inv a y z :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelXZ :
      SubgroupCentralizerRightQuotientClassifier mul inv a x z <->
        SubgroupCentralizerQuotientKernel mul inv a x z :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  exact Iff.mpr classifierKernelXZ
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_trans_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY xy) (Iff.mp classifierKernelYZ yz))

end BEDC.Derived.SubgroupUp
