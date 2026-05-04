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

theorem SubgroupCentralizerRightQuotientClassifier_hsame_transport
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x x' y y' : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y -> hsame x x' ->
      hsame y y' -> SubgroupCentralizerRightQuotientClassifier mul inv a x' y' := by
  intro classified sameXX' sameYY'
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelX'Y' :
      SubgroupCentralizerRightQuotientClassifier mul inv a x' y' <->
        SubgroupCentralizerQuotientKernel mul inv a x' y' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have transported : SubgroupCentralizerQuotientKernel mul inv a x' y' :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_hsame_transport
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY classified) sameXX' sameYY'
  exact Iff.mpr classifierKernelX'Y' transported

protected theorem SubgroupCentralizerRightQuotientClassifier_symm_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x y ->
      SubgroupCentralizerRightQuotientClassifier mul inv a y x := by
  intro classified
  have classifierKernelXY :
      SubgroupCentralizerRightQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have classifierKernelYX :
      SubgroupCentralizerRightQuotientClassifier mul inv a y x <->
        SubgroupCentralizerQuotientKernel mul inv a y x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  exact Iff.mpr classifierKernelYX
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_symm_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv
      (Iff.mp classifierKernelXY classified))

end BEDC.Derived.SubgroupUp
