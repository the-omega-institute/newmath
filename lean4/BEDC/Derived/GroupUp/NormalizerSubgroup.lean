import BEDC.Derived.GroupUp.CentralizerNormalizer

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_centralizer_normalizer_subgroup_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    let Centralizer := fun y : BHist => hsame (mul y a) (mul a y)
    let Conj := fun u y : BHist => mul (mul u y) (inv u)
    let Normalizer := fun u : BHist =>
      (forall y : BHist, Centralizer y -> Centralizer (Conj u y)) ∧
        (forall y : BHist, Centralizer y -> Centralizer (Conj (inv u) y))
    Normalizer BHist.Empty ∧
      (forall {s t : BHist}, Normalizer s -> Normalizer t -> Normalizer (mul s t)) ∧
      (forall {s : BHist}, Normalizer s -> Normalizer (inv s)) ∧
      (forall {s t : BHist}, Normalizer s -> hsame s t -> Normalizer t) ∧
      (forall {s : BHist}, Centralizer s -> Normalizer s) := by
  dsimp
  have centralizerTransport :
      forall {p q : BHist}, hsame p q -> hsame (mul p a) (mul a p) ->
        hsame (mul q a) (mul a q) := by
    intro p q samePQ centralP
    exact hsame_trans (mulCongr (hsame_symm samePQ) (hsame_refl a))
      (hsame_trans centralP (mulCongr (hsame_refl a) samePQ))
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv
  have conjParameterTransport :
      forall {u v x : BHist}, hsame u v ->
        hsame (mul (mul u x) (inv u)) (mul (mul v x) (inv v)) := by
    intro u v x sameUV
    exact mulCongr (mulCongr sameUV (hsame_refl x)) (invCongr sameUV)
  have centralizerMulClosed :
      forall {x y : BHist}, hsame (mul x a) (mul a x) ->
        hsame (mul y a) (mul a y) -> hsame (mul (mul x y) a) (mul a (mul x y)) := by
    intro x y centralX centralY
    exact BEDC.Derived.GroupUp.group_centralizer_mul_closed_from_empty_unit
      assocC rightId mulCongr
      centralX centralY
  have centralizerInvClosed :
      forall {x : BHist}, hsame (mul x a) (mul a x) ->
        hsame (mul (inv x) a) (mul a (inv x)) := by
    intro x centralX
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralX
  have includeCentralizer :
      forall {s : BHist}, hsame (mul s a) (mul a s) ->
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul s y) (inv s)) a)
            (mul a (mul (mul s y) (inv s)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
            (mul a (mul (mul (inv s) y) (inv (inv s)))))) := by
    intro s centralS
    have centralInvS : hsame (mul (inv s) a) (mul a (inv s)) :=
      centralizerInvClosed centralS
    have centralInvInvS : hsame (mul (inv (inv s)) a) (mul a (inv (inv s))) :=
      centralizerInvClosed centralInvS
    constructor
    · intro y centralY
      exact centralizerMulClosed (centralizerMulClosed centralS centralY) centralInvS
    · intro y centralY
      exact centralizerMulClosed (centralizerMulClosed centralInvS centralY) centralInvInvS
  have normalizerTransport :
      forall {s t : BHist},
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul s y) (inv s)) a)
            (mul a (mul (mul s y) (inv s)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
            (mul a (mul (mul (inv s) y) (inv (inv s)))))) ->
        hsame s t ->
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul t y) (inv t)) a)
            (mul a (mul (mul t y) (inv t)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv t) y) (inv (inv t))) a)
            (mul a (mul (mul (inv t) y) (inv (inv t)))))) := by
    intro s t normalizesS sameST
    constructor
    · intro y centralY
      exact centralizerTransport (conjParameterTransport sameST)
        (normalizesS.left y centralY)
    · intro y centralY
      exact centralizerTransport (conjParameterTransport (invCongr sameST))
        (normalizesS.right y centralY)
  have productClosed :
      forall {s t : BHist},
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul s y) (inv s)) a)
            (mul a (mul (mul s y) (inv s)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
            (mul a (mul (mul (inv s) y) (inv (inv s)))))) ->
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul t y) (inv t)) a)
            (mul a (mul (mul t y) (inv t)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv t) y) (inv (inv t))) a)
            (mul a (mul (mul (inv t) y) (inv (inv t)))))) ->
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (mul s t) y) (inv (mul s t))) a)
            (mul a (mul (mul (mul s t) y) (inv (mul s t))))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv (mul s t)) y) (inv (inv (mul s t)))) a)
            (mul a (mul (mul (inv (mul s t)) y) (inv (inv (mul s t))))))) := by
    intro s t normalizesS normalizesT
    constructor
    · intro y centralY
      have composed :=
        BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
          assocC leftId rightId mulCongr leftInv rightInv
          (a := a) (s := s) (t := t) (x := y) normalizesS normalizesT centralY
      exact centralizerTransport (hsame_symm composed.right.left) composed.left
    · intro y centralY
      have composed :=
        BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
          assocC leftId rightId mulCongr leftInv rightInv
          (a := a) (s := s) (t := t) (x := y) normalizesS normalizesT centralY
      exact centralizerTransport (hsame_symm composed.right.right.right)
        composed.right.right.left
  have inverseClosed :
      forall {s : BHist},
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul s y) (inv s)) a)
            (mul a (mul (mul s y) (inv s)))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
            (mul a (mul (mul (inv s) y) (inv (inv s)))))) ->
        ((forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
            (mul a (mul (mul (inv s) y) (inv (inv s))))) ∧
        (forall y : BHist, hsame (mul y a) (mul a y) ->
          hsame (mul (mul (mul (inv (inv s)) y) (inv (inv (inv s)))) a)
            (mul a (mul (mul (inv (inv s)) y) (inv (inv (inv s))))))) := by
    intro s normalizesS
    constructor
    · intro y centralY
      exact normalizesS.right y centralY
    · intro y centralY
      have sameInvInvS : hsame (inv (inv s)) s :=
        group_left_inverse_involutive assocC leftId rightId mulCongr leftInv s
      exact centralizerTransport (hsame_symm (conjParameterTransport sameInvInvS))
        (normalizesS.left y centralY)
  have emptyCentral : hsame (mul BHist.Empty a) (mul a BHist.Empty) :=
    group_centralizer_empty_unit_mem leftId rightId
  exact And.intro (includeCentralizer emptyCentral)
    (And.intro productClosed
      (And.intro inverseClosed (And.intro normalizerTransport includeCentralizer)))

end BEDC.Derived.GroupUp
