import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerNormalizer_certificate_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SubgroupCentralizerNormalizer mul inv a BHist.Empty ∧
      (forall {s t : BHist}, SubgroupCentralizerNormalizer mul inv a s ->
        SubgroupCentralizerNormalizer mul inv a t ->
          SubgroupCentralizerNormalizer mul inv a (mul s t)) ∧
      (forall {t : BHist}, SubgroupCentralizerNormalizer mul inv a t ->
        SubgroupCentralizerNormalizer mul inv a (inv t)) ∧
      (forall {s t : BHist}, SubgroupCentralizerNormalizer mul inv a s ->
        hsame s t -> SubgroupCentralizerNormalizer mul inv a t) ∧
      (forall {t : BHist}, SubgroupCentralizerCarrier mul a t ->
        SubgroupCentralizerNormalizer mul inv a t) := by
  have rows := BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
    assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    rows.right.right.right.right
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    BEDC.Derived.GroupUp.group_inverse_congruence_from_laws
      assocC leftId rightId mulCongr leftInv rightInv
  have includeCentralizer :
      forall {t : BHist}, SubgroupCentralizerCarrier mul a t ->
        SubgroupCentralizerNormalizer mul inv a t := by
    intro t centralT
    exact SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralT
  have normalizerTransport :
      forall {s t : BHist}, SubgroupCentralizerNormalizer mul inv a s ->
        hsame s t -> SubgroupCentralizerNormalizer mul inv a t := by
    intro s t normalizesS sameST
    constructor
    · intro x centralX
      have sameWord : hsame (mul (mul s x) (inv s)) (mul (mul t x) (inv t)) :=
        mulCongr (mulCongr sameST (hsame_refl x)) (invCongr sameST)
      exact carrierTransport (normalizesS.left x centralX) sameWord
    · intro x centralX
      have sameInv : hsame (inv s) (inv t) := invCongr sameST
      have sameWord : hsame (mul (mul (inv s) x) (inv (inv s)))
          (mul (mul (inv t) x) (inv (inv t))) :=
        mulCongr (mulCongr sameInv (hsame_refl x)) (invCongr sameInv)
      exact carrierTransport (normalizesS.right x centralX) sameWord
  have invClosed :
      forall {t : BHist}, SubgroupCentralizerNormalizer mul inv a t ->
        SubgroupCentralizerNormalizer mul inv a (inv t) := by
    intro t normalizesT
    constructor
    · intro x centralX
      exact normalizesT.right x centralX
    · intro x centralX
      have invInvSameT : hsame (inv (inv t)) t :=
        BEDC.Derived.GroupUp.group_left_inverse_involutive
          assocC leftId rightId mulCongr leftInv t
      have invInvInvSameInvT : hsame (inv (inv (inv t))) (inv t) :=
        invCongr invInvSameT
      have sameWord : hsame (mul (mul t x) (inv t))
          (mul (mul (inv (inv t)) x) (inv (inv (inv t)))) :=
        mulCongr (mulCongr (hsame_symm invInvSameT) (hsame_refl x))
          (hsame_symm invInvInvSameInvT)
      exact carrierTransport (normalizesT.left x centralX) sameWord
  exact And.intro (includeCentralizer rows.right.left)
    (And.intro (BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv)
      (And.intro invClosed (And.intro normalizerTransport includeCentralizer)))

end BEDC.Derived.SubgroupUp
