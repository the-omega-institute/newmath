import BEDC.Derived.GroupUp.ConjugationClassifier
import BEDC.Derived.GroupUp.NormalizerRoundtrip

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_centralizer_normalizer_conjugation_automorphism_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s : BHist} :
    let Centralizer := fun x : BHist => hsame (mul x a) (mul a x)
    let Conj := fun u x : BHist => mul (mul u x) (inv u)
    let Normalizer := fun u : BHist =>
      (forall x : BHist, Centralizer x -> Centralizer (Conj u x)) ∧
      (forall x : BHist, Centralizer x -> Centralizer (Conj (inv u) x))
    Normalizer s ->
      (forall x : BHist, Centralizer x -> Centralizer (Conj s x)) ∧
      (forall y : BHist, Centralizer y ->
        Centralizer (Conj (inv s) y) ∧ hsame (Conj s (Conj (inv s) y)) y) ∧
      (forall x y : BHist, Centralizer x -> Centralizer y ->
        (hsame (Conj s x) (Conj s y) <-> hsame x y)) := by
  dsimp
  intro normalizesS
  constructor
  · intro x centralX
    exact normalizesS.left x centralX
  · constructor
    · intro y centralY
      have roundtrip :=
        BEDC.Derived.GroupUp.group_normalizer_conjugation_inverse_roundtrip_from_empty_unit
          assocC leftId rightId mulCongr leftInv rightInv
          (a := a) (s := s) (x := y) normalizesS centralY
      exact And.intro roundtrip.right.left roundtrip.right.right.right
    · intro x y _centralX _centralY
      exact BEDC.Derived.GroupUp.group_conjugation_classifier_exact_from_empty_unit_iff
        assocC leftId rightId mulCongr leftInv rightInv

end BEDC.Derived.GroupUp
