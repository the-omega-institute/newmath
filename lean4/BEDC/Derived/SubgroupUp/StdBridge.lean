import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubgroupUp_StdBridge {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty) {a x : BHist} :
    SubgroupCentralizerNormalizer mul inv a x ->
      SemanticNameCert (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerClassifier mul a) ∧
        SubgroupCentralizerQuotientClassifier mul inv a x x ∧
          SubgroupCentralizerRightQuotientClassifier mul inv a x x ∧
            SubgroupCentralizerRightCosetClassifier mul inv a x x ∧
              SubgroupCentralizerQuotientKernel mul inv a x x := by
  intro normalizes
  have semanticCert :
      SemanticNameCert (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerCarrier mul a) (SubgroupCentralizerCarrier mul a)
        (SubgroupCentralizerClassifier mul a) :=
    SubgroupCentralizer_semanticNameCert (mul := mul) (a := a) leftId rightId
  have kernel :
      SubgroupCentralizerQuotientKernel mul inv a x x :=
    SubgroupCentralizerNormalizer_kernel_classifier_refl assocC leftId rightId mulCongr
      leftInv rightInv normalizes
  have quotient :
      SubgroupCentralizerQuotientClassifier mul inv a x x :=
    (SubgroupCentralizerQuotientClassifier_kernel_iff assocC leftId rightId mulCongr leftInv
      rightInv).mpr kernel
  have rightQuotient :
      SubgroupCentralizerRightQuotientClassifier mul inv a x x :=
    (SubgroupCentralizerRightQuotientClassifier_kernel_iff assocC leftId rightId mulCongr
      leftInv rightInv).mpr kernel
  have rightCoset :
      SubgroupCentralizerRightCosetClassifier mul inv a x x :=
    (SubgroupCentralizerRightCosetClassifier_quotientKernel_iff assocC leftId mulCongr
      leftInv rightInv).mpr kernel
  exact
    And.intro semanticCert
      (And.intro quotient
        (And.intro rightQuotient (And.intro rightCoset kernel)))

end BEDC.Derived.SubgroupUp
