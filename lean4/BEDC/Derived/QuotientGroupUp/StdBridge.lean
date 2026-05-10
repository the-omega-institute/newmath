import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp

theorem QuotientGroupUp_StdBridge
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    SubgroupCentralizerNormalizer mul inv a x ->
      SubgroupCentralizerNormalizer mul inv a y ->
        let w := mul (inv x) y
        (SubgroupCentralizerQuotientKernel mul inv a x y <->
          SubgroupCentralizerQuotientKernel mul inv a BHist.Empty w) ∧
        (SubgroupCentralizerQuotientClassifier mul inv a x y <->
          SubgroupCentralizerQuotientKernel mul inv a BHist.Empty w) ∧
        (SubgroupCentralizerRightCosetClassifier mul inv a x y <->
          SubgroupCentralizerQuotientKernel mul inv a BHist.Empty w) := by
  intro normalizesX normalizesY
  dsimp
  have emptyFiber :
      SubgroupCentralizerQuotientKernel mul inv a BHist.Empty (mul (inv x) y) <->
        SubgroupCentralizerCarrier mul a (mul (inv x) y) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_empty_fiber_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have kernelFiber :
      SubgroupCentralizerQuotientKernel mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a BHist.Empty (mul (inv x) y) := by
    constructor
    · intro kernel
      exact Iff.mpr emptyFiber kernel.right.right
    · intro fiberKernel
      exact And.intro normalizesX
        (And.intro normalizesY (Iff.mp emptyFiber fiberKernel))
  have quotientKernel :
      SubgroupCentralizerQuotientClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientClassifier_kernel_iff
      assocC leftId rightId mulCongr leftInv rightInv
  have rightCosetKernel :
      SubgroupCentralizerRightCosetClassifier mul inv a x y <->
        SubgroupCentralizerQuotientKernel mul inv a x y :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerRightCosetClassifier_quotientKernel_iff
      assocC leftId mulCongr leftInv rightInv
  constructor
  · exact kernelFiber
  · constructor
    · constructor
      · intro classified
        exact Iff.mp kernelFiber (Iff.mp quotientKernel classified)
      · intro fiberKernel
        exact Iff.mpr quotientKernel (Iff.mpr kernelFiber fiberKernel)
    · constructor
      · intro classified
        exact Iff.mp kernelFiber (Iff.mp rightCosetKernel classified)
      · intro fiberKernel
        exact Iff.mpr rightCosetKernel (Iff.mpr kernelFiber fiberKernel)

end BEDC.Derived.QuotientGroupUp
