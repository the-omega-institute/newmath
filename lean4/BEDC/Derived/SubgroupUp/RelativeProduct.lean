import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerNormalizer_relative_product_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty) {a s t : BHist} :
    SubgroupCentralizerNormalizer mul inv a s ->
      SubgroupCentralizerNormalizer mul inv a t ->
        SubgroupCentralizerNormalizer mul inv a (mul (inv s) t) := by
  intro normalizesS normalizesT
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have invInvSameS : hsame (inv (inv s)) s :=
    BEDC.Derived.GroupUp.group_left_inverse_involutive assocC leftId rightId mulCongr
      leftInv s
  have invTripleSameInvS : hsame (inv (inv (inv s))) (inv s) :=
    BEDC.Derived.GroupUp.group_left_inverse_involutive assocC leftId rightId mulCongr
      leftInv (inv s)
  have normalizesInvS : SubgroupCentralizerNormalizer mul inv a (inv s) := by
    constructor
    · intro x centralX
      exact normalizesS.right x centralX
    · intro x centralX
      have sameConjugate :
          hsame (mul (mul s x) (inv s))
            (mul (mul (inv (inv s)) x) (inv (inv (inv s)))) :=
        mulCongr (mulCongr (hsame_symm invInvSameS) (hsame_refl x))
          (hsame_symm invTripleSameInvS)
      exact carrierTransport (normalizesS.left x centralX) sameConjugate
  exact BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
    assocC leftId rightId mulCongr leftInv rightInv normalizesInvS normalizesT

end BEDC.Derived.SubgroupUp
