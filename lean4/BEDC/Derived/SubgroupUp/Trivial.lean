import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SubgroupTrivialCarrier (e x : BHist) : Prop :=
  hsame x e

def SubgroupTrivialClassifier (e x y : BHist) : Prop :=
  SubgroupTrivialCarrier e x ∧ SubgroupTrivialCarrier e y ∧ hsame x y

theorem SubgroupTrivialCarrier_certificate
    {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    {e : BHist}
    (leftId : forall x : BHist, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (invCongr : forall {x y : BHist}, hsame x y -> hsame (inv x) (inv y))
    (invId : hsame (inv e) e) :
    SemanticNameCert (SubgroupTrivialCarrier e) (SubgroupTrivialCarrier e)
        (SubgroupTrivialCarrier e) (SubgroupTrivialClassifier e) ∧
      SubgroupTrivialCarrier e e ∧
        (forall {x y : BHist}, SubgroupTrivialCarrier e x ->
          SubgroupTrivialCarrier e y -> SubgroupTrivialCarrier e (mul x y)) ∧
        (forall {x : BHist}, SubgroupTrivialCarrier e x ->
          SubgroupTrivialCarrier e (inv x)) ∧
        (forall {x y : BHist}, SubgroupTrivialCarrier e x -> hsame x y ->
          SubgroupTrivialCarrier e y) ∧
        (forall {x x' y y' : BHist}, SubgroupTrivialClassifier e x x' ->
          SubgroupTrivialClassifier e y y' ->
            SubgroupTrivialClassifier e (mul x y) (mul x' y')) ∧
        (forall {x y : BHist}, SubgroupTrivialClassifier e x y ->
          SubgroupTrivialClassifier e (inv x) (inv y)) := by
  have carrierE : SubgroupTrivialCarrier e e := hsame_refl e
  have mulClosed :
      forall {x y : BHist}, SubgroupTrivialCarrier e x ->
        SubgroupTrivialCarrier e y -> SubgroupTrivialCarrier e (mul x y) := by
    intro x y carrierX carrierY
    exact hsame_trans (mulCongr carrierX carrierY) (leftId e)
  have invClosed :
      forall {x : BHist}, SubgroupTrivialCarrier e x ->
        SubgroupTrivialCarrier e (inv x) := by
    intro x carrierX
    exact hsame_trans (invCongr carrierX) invId
  have carrierTransport :
      forall {x y : BHist}, SubgroupTrivialCarrier e x -> hsame x y ->
        SubgroupTrivialCarrier e y := by
    intro x y carrierX sameXY
    exact hsame_trans (hsame_symm sameXY) carrierX
  have classifierMul :
      forall {x x' y y' : BHist}, SubgroupTrivialClassifier e x x' ->
        SubgroupTrivialClassifier e y y' ->
          SubgroupTrivialClassifier e (mul x y) (mul x' y') := by
    intro x x' y y' classifiedX classifiedY
    exact And.intro
      (mulClosed classifiedX.left classifiedY.left)
      (And.intro
        (mulClosed classifiedX.right.left classifiedY.right.left)
        (mulCongr classifiedX.right.right classifiedY.right.right))
  have classifierInv :
      forall {x y : BHist}, SubgroupTrivialClassifier e x y ->
        SubgroupTrivialClassifier e (inv x) (inv y) := by
    intro x y classified
    exact And.intro (invClosed classified.left)
      (And.intro (invClosed classified.right.left) (invCongr classified.right.right))
  have cert :
      SemanticNameCert (SubgroupTrivialCarrier e) (SubgroupTrivialCarrier e)
        (SubgroupTrivialCarrier e) (SubgroupTrivialClassifier e) := {
    core := {
      carrier_inhabited := Exists.intro e carrierE
      equiv_refl := by
        intro h carrierH
        exact And.intro carrierH (And.intro carrierH (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _carrierH
        exact classified.right.left
    }
    pattern_sound := by
      intro h carrierH
      exact carrierH
    ledger_sound := by
      intro h carrierH
      exact carrierH
  }
  exact And.intro cert
    (And.intro carrierE
      (And.intro mulClosed
        (And.intro invClosed
          (And.intro carrierTransport (And.intro classifierMul classifierInv)))))

end BEDC.Derived.SubgroupUp
