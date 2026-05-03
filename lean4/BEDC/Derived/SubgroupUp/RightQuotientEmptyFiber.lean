import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

theorem SubgroupCentralizerRightQuotientClassifier_empty_fiber_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a BHist.Empty x <->
      SubgroupCentralizerCarrier mul a x := by
  have classifierKernel :
      SubgroupCentralizerRightQuotientClassifier mul inv a BHist.Empty x <->
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have kernelFiber :
      SubgroupCentralizerQuotientKernel mul inv a BHist.Empty x <->
        SubgroupCentralizerCarrier mul a x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  constructor
  · intro classified
    exact Iff.mp kernelFiber (Iff.mp classifierKernel classified)
  · intro centralX
    exact Iff.mpr classifierKernel (Iff.mpr kernelFiber centralX)

theorem SubgroupCentralizerRightQuotientClassifier_empty_right_fiber_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    SubgroupCentralizerRightQuotientClassifier mul inv a x BHist.Empty <->
      SubgroupCentralizerCarrier mul a x := by
  have classifierKernel :
      SubgroupCentralizerRightQuotientClassifier mul inv a x BHist.Empty <->
        SubgroupCentralizerQuotientKernel mul inv a x BHist.Empty :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have kernelFiber :
      SubgroupCentralizerQuotientKernel mul inv a x BHist.Empty <->
        SubgroupCentralizerCarrier mul a x :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_right_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  constructor
  · intro classified
    exact Iff.mp kernelFiber (Iff.mp classifierKernel classified)
  · intro centralX
    exact Iff.mpr classifierKernel (Iff.mpr kernelFiber centralX)

end BEDC.Derived.SubgroupUp
