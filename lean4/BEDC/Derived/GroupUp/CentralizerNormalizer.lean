import BEDC.Derived.GroupUp
import BEDC.Derived.GroupUp.Centralizer

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_conjugation_empty_action_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {x : BHist} :
    hsame (mul (mul BHist.Empty x) (inv BHist.Empty)) x := by
  have invEmpty : hsame (inv BHist.Empty) BHist.Empty := by
    exact hsame_trans (hsame_symm (leftId (inv BHist.Empty))) (rightInv BHist.Empty)
  exact hsame_trans (mulCongr (leftId x) invEmpty) (rightId x)

protected theorem group_normalizer_conjugation_action_composition_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t x : BHist} :
    let Centralizer := fun y : BHist => hsame (mul y a) (mul a y)
    let Conj := fun u y : BHist => mul (mul u y) (inv u)
    let Normalizer := fun u : BHist =>
      (forall y : BHist, Centralizer y -> Centralizer (Conj u y)) ∧
        (forall y : BHist, Centralizer y -> Centralizer (Conj (inv u) y))
    Normalizer s -> Normalizer t -> Centralizer x ->
      Centralizer (Conj s (Conj t x)) ∧
        hsame (Conj (mul s t) x) (Conj s (Conj t x)) ∧
        Centralizer (Conj (inv t) (Conj (inv s) x)) ∧
        hsame (Conj (inv (mul s t)) x) (Conj (inv t) (Conj (inv s) x)) := by
  dsimp
  intro normS normT centralX
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv
  have conjCongrLeft :
      forall {u v y : BHist}, hsame u v ->
        hsame (mul (mul u y) (inv u)) (mul (mul v y) (inv v)) := by
    intro u v y sameUV
    exact mulCongr (mulCongr sameUV (hsame_refl y)) (invCongr sameUV)
  have conjCompose :
      forall u v y : BHist,
        hsame (mul (mul (mul u v) y) (inv (mul u v)))
          (mul (mul u (mul (mul v y) (inv v))) (inv u)) := by
    intro u v y
    have reverseInv : hsame (inv (mul u v)) (mul (inv v) (inv u)) :=
      group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv u v
    have reassocHead :
        hsame (mul (mul (mul u v) y) (inv (mul u v)))
          (mul (mul u (mul v y)) (inv (mul u v))) := by
      exact mulCongr (assocC u v y) (hsame_refl (inv (mul u v)))
    have replaceInv :
        hsame (mul (mul u (mul v y)) (inv (mul u v)))
          (mul (mul u (mul v y)) (mul (inv v) (inv u))) := by
      exact mulCongr (hsame_refl (mul u (mul v y))) reverseInv
    have reassocTail :
        hsame (mul (mul u (mul v y)) (mul (inv v) (inv u)))
          (mul (mul (mul u (mul v y)) (inv v)) (inv u)) := by
      exact hsame_symm (assocC (mul u (mul v y)) (inv v) (inv u))
    have reassocMiddle :
        hsame (mul (mul (mul u (mul v y)) (inv v)) (inv u))
          (mul (mul u (mul (mul v y) (inv v))) (inv u)) := by
      exact mulCongr (assocC u (mul v y) (inv v)) (hsame_refl (inv u))
    exact hsame_trans reassocHead
      (hsame_trans replaceInv (hsame_trans reassocTail reassocMiddle))
  have centralTX : hsame (mul (mul (mul t x) (inv t)) a)
      (mul a (mul (mul t x) (inv t))) :=
    normT.left x centralX
  have centralSTX : hsame (mul (mul (mul s (mul (mul t x) (inv t))) (inv s)) a)
      (mul a (mul (mul s (mul (mul t x) (inv t))) (inv s))) :=
    normS.left (mul (mul t x) (inv t)) centralTX
  have centralInvSX : hsame (mul (mul (mul (inv s) x) (inv (inv s))) a)
      (mul a (mul (mul (inv s) x) (inv (inv s)))) :=
    normS.right x centralX
  have centralInvTInvSX :
      hsame
        (mul (mul (mul (inv t) (mul (mul (inv s) x) (inv (inv s))))
          (inv (inv t))) a)
        (mul a
          (mul (mul (inv t) (mul (mul (inv s) x) (inv (inv s))))
            (inv (inv t)))) :=
    normT.right (mul (mul (inv s) x) (inv (inv s))) centralInvSX
  have composeST :
      hsame (mul (mul (mul s t) x) (inv (mul s t)))
        (mul (mul s (mul (mul t x) (inv t))) (inv s)) :=
    conjCompose s t x
  have reverseST : hsame (inv (mul s t)) (mul (inv t) (inv s)) :=
    group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv s t
  have replaceInverseComposite :
      hsame (mul (mul (inv (mul s t)) x) (inv (inv (mul s t))))
        (mul (mul (mul (inv t) (inv s)) x) (inv (mul (inv t) (inv s)))) := by
    exact conjCongrLeft reverseST
  have composeInvTInvS :
      hsame (mul (mul (mul (inv t) (inv s)) x) (inv (mul (inv t) (inv s))))
        (mul (mul (inv t) (mul (mul (inv s) x) (inv (inv s)))) (inv (inv t))) :=
    conjCompose (inv t) (inv s) x
  exact And.intro centralSTX
    (And.intro composeST
      (And.intro centralInvTInvSX
        (hsame_trans replaceInverseComposite composeInvTInvS)))

theorem group_centralizer_normalizer_forward_action_composition_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s t x : BHist}
    (normalizesS : forall y : BHist, hsame (mul y a) (mul a y) ->
      hsame (mul (mul (mul s y) (inv s)) a)
        (mul a (mul (mul s y) (inv s))))
    (normalizesT : forall y : BHist, hsame (mul y a) (mul a y) ->
      hsame (mul (mul (mul t y) (inv t)) a)
        (mul a (mul (mul t y) (inv t))))
    (centralX : hsame (mul x a) (mul a x)) :
      hsame (mul (mul (mul s (mul (mul t x) (inv t))) (inv s)) a)
        (mul a (mul (mul s (mul (mul t x) (inv t))) (inv s))) ∧
      hsame (mul (mul (mul s t) x) (inv (mul s t)))
        (mul (mul s (mul (mul t x) (inv t))) (inv s)) := by
  have centralAfterT :
      hsame (mul (mul (mul t x) (inv t)) a)
        (mul a (mul (mul t x) (inv t))) :=
    normalizesT x centralX
  have centralAfterS :
      hsame (mul (mul (mul s (mul (mul t x) (inv t))) (inv s)) a)
        (mul a (mul (mul s (mul (mul t x) (inv t))) (inv s))) :=
    normalizesS (mul (mul t x) (inv t)) centralAfterT
  have inverseProduct :
      hsame (inv (mul s t)) (mul (inv t) (inv s)) :=
    group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv s t
  have replaceInverse :
      hsame (mul (mul (mul s t) x) (inv (mul s t)))
        (mul (mul (mul s t) x) (mul (inv t) (inv s))) :=
    mulCongr (hsame_refl (mul (mul s t) x)) inverseProduct
  have exposeTail :
      hsame (mul (mul (mul s t) x) (mul (inv t) (inv s)))
        (mul (mul (mul (mul s t) x) (inv t)) (inv s)) :=
    hsame_symm (assocC (mul (mul s t) x) (inv t) (inv s))
  have reassocHead :
      hsame (mul (mul (mul s t) x) (inv t))
        (mul s (mul (mul t x) (inv t))) :=
    hsame_trans
      (mulCongr (assocC s t x) (hsame_refl (inv t)))
      (assocC s (mul t x) (inv t))
  have nestedWord :
      hsame (mul (mul (mul (mul s t) x) (inv t)) (inv s))
        (mul (mul s (mul (mul t x) (inv t))) (inv s)) :=
    mulCongr reassocHead (hsame_refl (inv s))
  exact And.intro centralAfterS
    (hsame_trans replaceInverse (hsame_trans exposeTail nestedWord))

protected theorem group_center_normal_subgroup_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty) :
    let Center := fun x : BHist => forall a : BHist, hsame (mul x a) (mul a x)
    let Conj := fun s x : BHist => mul (mul s x) (inv s)
    let Centralizer := fun a x : BHist => hsame (mul x a) (mul a x)
    let Normalizer := fun a s : BHist =>
      (forall x : BHist, Centralizer a x -> Centralizer a (Conj s x)) ∧
        (forall x : BHist, Centralizer a x -> Centralizer a (Conj (inv s) x))
    Center BHist.Empty ∧ (forall {x y : BHist}, Center x -> Center y -> Center (mul x y)) ∧
      (forall {x : BHist}, Center x -> Center (inv x)) ∧
      (forall {x y : BHist}, Center x -> hsame x y -> Center y) ∧
      (forall {s x : BHist}, Center x -> Center (Conj s x)) ∧
      (forall {a x : BHist}, Center x -> Centralizer a x ∧ Normalizer a x) := by
  dsimp
  have centralizerTransport :
      forall {a p q : BHist}, hsame p q -> hsame (mul p a) (mul a p) ->
        hsame (mul q a) (mul a q) := by
    intro a p q samePQ centralP
    exact hsame_trans (mulCongr (hsame_symm samePQ) (hsame_refl a))
      (hsame_trans centralP (mulCongr (hsame_refl a) samePQ))
  have centerTransport :
      forall {p q : BHist}, (forall a : BHist, hsame (mul p a) (mul a p)) ->
        hsame p q -> forall a : BHist, hsame (mul q a) (mul a q) := by
    intro p q centerP samePQ a
    exact centralizerTransport samePQ (centerP a)
  have centerInv :
      forall {x : BHist}, (forall a : BHist, hsame (mul x a) (mul a x)) ->
        forall a : BHist, hsame (mul (inv x) a) (mul a (inv x)) := by
    intro x centerX a
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a) (x := x) (centerX a)
  have conjFixedByCentralElement :
      forall s y : BHist, (forall a : BHist, hsame (mul s a) (mul a s)) ->
        hsame (mul (mul s y) (inv s)) y := by
    intro s y centerS
    have invCenterS : forall a : BHist, hsame (mul (inv s) a) (mul a (inv s)) :=
      centerInv centerS
    have reassocHead :
        hsame (mul (mul s y) (inv s)) (mul s (mul y (inv s))) :=
      assocC s y (inv s)
    have commuteTail :
        hsame (mul s (mul y (inv s))) (mul s (mul (inv s) y)) :=
      mulCongr (hsame_refl s) (hsame_symm (invCenterS y))
    have reassocTail :
        hsame (mul s (mul (inv s) y)) (mul (mul s (inv s)) y) :=
      hsame_symm (assocC s (inv s) y)
    have collapseHead :
        hsame (mul (mul s (inv s)) y) (mul BHist.Empty y) :=
      mulCongr (rightInv s) (hsame_refl y)
    exact hsame_trans reassocHead
      (hsame_trans commuteTail
        (hsame_trans reassocTail (hsame_trans collapseHead (leftId y))))
  have conjFixedCentralTarget :
      forall s x : BHist, (forall a : BHist, hsame (mul x a) (mul a x)) ->
        hsame (mul (mul s x) (inv s)) x := by
    intro s x centerX
    have reassocHead :
        hsame (mul (mul s x) (inv s)) (mul s (mul x (inv s))) :=
      assocC s x (inv s)
    have commuteTail :
        hsame (mul s (mul x (inv s))) (mul s (mul (inv s) x)) :=
      mulCongr (hsame_refl s) (centerX (inv s))
    have reassocTail :
        hsame (mul s (mul (inv s) x)) (mul (mul s (inv s)) x) :=
      hsame_symm (assocC s (inv s) x)
    have collapseHead :
        hsame (mul (mul s (inv s)) x) (mul BHist.Empty x) :=
      mulCongr (rightInv s) (hsame_refl x)
    exact hsame_trans reassocHead
      (hsame_trans commuteTail
        (hsame_trans reassocTail (hsame_trans collapseHead (leftId x))))
  constructor
  · intro a
    exact hsame_trans (leftId a) (hsame_symm (rightId a))
  · constructor
    · intro x y centerX centerY a
      have assocLeft : hsame (mul (mul x y) a) (mul x (mul y a)) :=
        assocC x y a
      have commuteY : hsame (mul x (mul y a)) (mul x (mul a y)) :=
        mulCongr (hsame_refl x) (centerY a)
      have reassocMiddle : hsame (mul x (mul a y)) (mul (mul x a) y) :=
        hsame_symm (assocC x a y)
      have commuteX : hsame (mul (mul x a) y) (mul (mul a x) y) :=
        mulCongr (centerX a) (hsame_refl y)
      have assocRight : hsame (mul (mul a x) y) (mul a (mul x y)) :=
        assocC a x y
      exact hsame_trans assocLeft
        (hsame_trans commuteY
          (hsame_trans reassocMiddle (hsame_trans commuteX assocRight)))
    · constructor
      · intro x centerX
        exact centerInv centerX
      · constructor
        · intro x y centerX sameXY
          exact centerTransport centerX sameXY
        · constructor
          · intro s x centerX
            exact centerTransport centerX (hsame_symm (conjFixedCentralTarget s x centerX))
          · intro a x centerX
            constructor
            · exact centerX a
            · constructor
              · intro y centralY
                have fixedConj := conjFixedByCentralElement x y centerX
                exact centralizerTransport (hsame_symm fixedConj) centralY
              · intro y centralY
                have centerInvX : forall q : BHist, hsame (mul (inv x) q) (mul q (inv x)) :=
                  centerInv centerX
                have fixedConj := conjFixedByCentralElement (inv x) y centerInvX
                exact centralizerTransport (hsame_symm fixedConj) centralY

protected theorem group_centralizer_normalizer_orbit_equivalence_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y z : BHist} :
    let Centralizer := fun q : BHist => hsame (mul q a) (mul a q)
    let Conj := fun s q : BHist => mul (mul s q) (inv s)
    let Normalizer := fun s : BHist =>
      (forall q : BHist, Centralizer q -> Centralizer (Conj s q)) ∧
        (forall q : BHist, Centralizer q -> Centralizer (Conj (inv s) q))
    let Orbit := fun p q : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer p ∧ Centralizer q ∧ hsame (Conj s p) q)
    Centralizer x -> Centralizer y -> Centralizer z ->
      Orbit x x ∧ (Orbit x y -> Orbit y x) ∧
        (Orbit x y -> Orbit y z -> Orbit x z) := by
  dsimp
  intro centralX centralY centralZ
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv
  have centralizerTransport :
      forall {p q : BHist}, hsame p q -> hsame (mul p a) (mul a p) ->
        hsame (mul q a) (mul a q) := by
    intro p q samePQ centralP
    exact hsame_trans (mulCongr (hsame_symm samePQ) (hsame_refl a))
      (hsame_trans centralP (mulCongr (hsame_refl a) samePQ))
  have conjCongrLeft :
      forall {u v q : BHist}, hsame u v ->
        hsame (mul (mul u q) (inv u)) (mul (mul v q) (inv v)) := by
    intro u v q sameUV
    exact mulCongr (mulCongr sameUV (hsame_refl q)) (invCongr sameUV)
  have conjCongrRight :
      forall {u p q : BHist}, hsame p q ->
        hsame (mul (mul u p) (inv u)) (mul (mul u q) (inv u)) := by
    intro u p q samePQ
    exact mulCongr (mulCongr (hsame_refl u) samePQ) (hsame_refl (inv u))
  have conjCompose :
      forall u v q : BHist,
        hsame (mul (mul (mul u v) q) (inv (mul u v)))
          (mul (mul u (mul (mul v q) (inv v))) (inv u)) := by
    intro u v q
    have reverseInv : hsame (inv (mul u v)) (mul (inv v) (inv u)) :=
      group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv u v
    have reassocHead :
        hsame (mul (mul (mul u v) q) (inv (mul u v)))
          (mul (mul u (mul v q)) (inv (mul u v))) := by
      exact mulCongr (assocC u v q) (hsame_refl (inv (mul u v)))
    have replaceInv :
        hsame (mul (mul u (mul v q)) (inv (mul u v)))
          (mul (mul u (mul v q)) (mul (inv v) (inv u))) := by
      exact mulCongr (hsame_refl (mul u (mul v q))) reverseInv
    have reassocTail :
        hsame (mul (mul u (mul v q)) (mul (inv v) (inv u)))
          (mul (mul (mul u (mul v q)) (inv v)) (inv u)) := by
      exact hsame_symm (assocC (mul u (mul v q)) (inv v) (inv u))
    have reassocMiddle :
        hsame (mul (mul (mul u (mul v q)) (inv v)) (inv u))
          (mul (mul u (mul (mul v q) (inv v))) (inv u)) := by
      exact mulCongr (assocC u (mul v q) (inv v)) (hsame_refl (inv u))
    exact hsame_trans reassocHead
      (hsame_trans replaceInv (hsame_trans reassocTail reassocMiddle))
  have unitAction : forall q : BHist,
      hsame (mul (mul BHist.Empty q) (inv BHist.Empty)) q := by
    intro q
    have invEmpty : hsame (inv BHist.Empty) BHist.Empty :=
      group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
    exact hsame_trans (mulCongr (leftId q) invEmpty) (rightId q)
  have emptyNormalizer :
      (forall q : BHist, hsame (mul q a) (mul a q) ->
        hsame (mul (mul (mul BHist.Empty q) (inv BHist.Empty)) a)
          (mul a (mul (mul BHist.Empty q) (inv BHist.Empty)))) ∧
      (forall q : BHist, hsame (mul q a) (mul a q) ->
        hsame (mul (mul (mul (inv BHist.Empty) q) (inv (inv BHist.Empty))) a)
          (mul a (mul (mul (inv BHist.Empty) q) (inv (inv BHist.Empty))))) := by
    constructor
    · intro q centralQ
      exact centralizerTransport (hsame_symm (unitAction q)) centralQ
    · intro q centralQ
      have invEmpty : hsame (inv BHist.Empty) BHist.Empty :=
        group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
      have sameAction :
          hsame (mul (mul (inv BHist.Empty) q) (inv (inv BHist.Empty)))
            (mul (mul BHist.Empty q) (inv BHist.Empty)) :=
        conjCongrLeft invEmpty
      exact centralizerTransport (hsame_symm (hsame_trans sameAction (unitAction q))) centralQ
  have inverseNormalizes :
      forall {s : BHist},
        ((forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul s q) (inv s)) a)
            (mul a (mul (mul s q) (inv s)))) ∧
        (forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv s) q) (inv (inv s))) a)
            (mul a (mul (mul (inv s) q) (inv (inv s)))))) ->
        ((forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv s) q) (inv (inv s))) a)
            (mul a (mul (mul (inv s) q) (inv (inv s))))) ∧
        (forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv (inv s)) q) (inv (inv (inv s)))) a)
            (mul a (mul (mul (inv (inv s)) q) (inv (inv (inv s))))))) := by
    intro s normS
    constructor
    · intro q centralQ
      exact normS.right q centralQ
    · intro q centralQ
      have invInvS : hsame (inv (inv s)) s :=
        group_left_inverse_involutive assocC leftId rightId mulCongr leftInv s
      have sameConj :
          hsame (mul (mul (inv (inv s)) q) (inv (inv (inv s))))
            (mul (mul s q) (inv s)) :=
        conjCongrLeft invInvS
      exact centralizerTransport (hsame_symm sameConj) (normS.left q centralQ)
  have inverseAction :
      forall s q : BHist,
        hsame (mul (mul (inv s) (mul (mul s q) (inv s))) (inv (inv s))) q := by
    intro s q
    have comp :
        hsame (mul (mul (mul (inv s) s) q) (inv (mul (inv s) s)))
          (mul (mul (inv s) (mul (mul s q) (inv s))) (inv (inv s))) :=
      conjCompose (inv s) s q
    have sameUnitHead :
        hsame (mul (mul (mul (inv s) s) q) (inv (mul (inv s) s)))
          (mul (mul BHist.Empty q) (inv BHist.Empty)) :=
      conjCongrLeft (leftInv s)
    exact hsame_trans (hsame_symm comp) (hsame_trans sameUnitHead (unitAction q))
  have compositeNormalizer :
      forall {s t : BHist},
        ((forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul s q) (inv s)) a)
            (mul a (mul (mul s q) (inv s)))) ∧
        (forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv s) q) (inv (inv s))) a)
            (mul a (mul (mul (inv s) q) (inv (inv s)))))) ->
        ((forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul t q) (inv t)) a)
            (mul a (mul (mul t q) (inv t)))) ∧
        (forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv t) q) (inv (inv t))) a)
            (mul a (mul (mul (inv t) q) (inv (inv t)))))) ->
        ((forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (mul t s) q) (inv (mul t s))) a)
            (mul a (mul (mul (mul t s) q) (inv (mul t s))))) ∧
        (forall q : BHist, hsame (mul q a) (mul a q) ->
          hsame (mul (mul (mul (inv (mul t s)) q) (inv (inv (mul t s)))) a)
            (mul a (mul (mul (inv (mul t s)) q) (inv (inv (mul t s))))))) := by
    intro s t normS normT
    constructor
    · intro q centralQ
      have data := BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv
        (a := a) (s := t) (t := s) (x := q) normT normS centralQ
      exact centralizerTransport (hsame_symm data.right.left) data.left
    · intro q centralQ
      have data := BEDC.Derived.GroupUp.group_normalizer_conjugation_action_composition_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv
        (a := a) (s := t) (t := s) (x := q) normT normS centralQ
      exact centralizerTransport (hsame_symm data.right.right.right) data.right.right.left
  constructor
  · exact Exists.intro BHist.Empty
      (And.intro emptyNormalizer
        (And.intro centralX (And.intro centralX (unitAction x))))
  · constructor
    · intro orbitXY
      cases orbitXY with
      | intro s orbitData =>
          have normInvS := inverseNormalizes orbitData.left
          have sameToConj :
              hsame (mul (mul (inv s) y) (inv (inv s)))
                (mul (mul (inv s) (mul (mul s x) (inv s))) (inv (inv s))) :=
            conjCongrRight (hsame_symm orbitData.right.right.right)
          have sameYX : hsame (mul (mul (inv s) y) (inv (inv s))) x :=
            hsame_trans sameToConj (inverseAction s x)
          exact Exists.intro (inv s)
            (And.intro normInvS
              (And.intro orbitData.right.right.left
                (And.intro orbitData.right.left sameYX)))
    · intro orbitXY orbitYZ
      cases orbitXY with
      | intro s dataXY =>
          cases orbitYZ with
          | intro t dataYZ =>
              have normTS := compositeNormalizer dataXY.left dataYZ.left
              have compTS :
                  hsame (mul (mul (mul t s) x) (inv (mul t s)))
                    (mul (mul t (mul (mul s x) (inv s))) (inv t)) :=
                conjCompose t s x
              have replaceMiddle :
                  hsame (mul (mul t (mul (mul s x) (inv s))) (inv t))
                    (mul (mul t y) (inv t)) :=
                conjCongrRight dataXY.right.right.right
              have sameXZ :
                  hsame (mul (mul (mul t s) x) (inv (mul t s))) z :=
                hsame_trans compTS
                  (hsame_trans replaceMiddle dataYZ.right.right.right)
              exact Exists.intro (mul t s)
                (And.intro normTS
                  (And.intro dataXY.right.left
                    (And.intro dataYZ.right.right.left sameXZ)))

protected theorem group_centralizer_normalizer_orbit_endpoint_transport_from_empty_unit_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (invCongr : forall {x y : BHist}, hsame x y -> hsame (inv x) (inv y))
    {a x y x' y' : BHist} :
    let Centralizer := fun q : BHist => hsame (mul q a) (mul a q)
    let Conj := fun s q : BHist => mul (mul s q) (inv s)
    let Normalizer := fun s : BHist =>
      (forall q : BHist, Centralizer q -> Centralizer (Conj s q)) ∧
        (forall q : BHist, Centralizer q -> Centralizer (Conj (inv s) q))
    let Orbit := fun p q : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer p ∧ Centralizer q ∧ hsame (Conj s p) q)
    Centralizer x -> Centralizer y -> Centralizer x' -> Centralizer y' ->
      hsame x x' -> hsame y y' -> (Orbit x y <-> Orbit x' y') := by
  dsimp
  intro centralX centralY centralX' centralY' sameXX' sameYY'
  have _unitStable : hsame (mul (mul BHist.Empty BHist.Empty) BHist.Empty) BHist.Empty :=
    hsame_trans (mulCongr (leftId BHist.Empty) (hsame_refl BHist.Empty))
      (rightId BHist.Empty)
  have _invStable : hsame (inv BHist.Empty) (inv BHist.Empty) :=
    invCongr (hsame_refl BHist.Empty)
  have conjEndpointTransport :
      forall {s p q : BHist}, hsame p q ->
        hsame (mul (mul s p) (inv s)) (mul (mul s q) (inv s)) := by
    intro s p q samePQ
    exact mulCongr (mulCongr (hsame_refl s) samePQ) (hsame_refl (inv s))
  constructor
  · intro orbitXY
    cases orbitXY with
    | intro s data =>
        have sameConj : hsame (mul (mul s x') (inv s)) (mul (mul s x) (inv s)) :=
          conjEndpointTransport (hsame_symm sameXX')
        have endpoint : hsame (mul (mul s x') (inv s)) y' :=
          hsame_trans sameConj (hsame_trans data.right.right.right sameYY')
        exact Exists.intro s
          (And.intro data.left (And.intro centralX' (And.intro centralY' endpoint)))
  · intro orbitX'Y'
    cases orbitX'Y' with
    | intro s data =>
        have sameConj : hsame (mul (mul s x) (inv s)) (mul (mul s x') (inv s)) :=
          conjEndpointTransport sameXX'
        have endpoint : hsame (mul (mul s x) (inv s)) y :=
          hsame_trans sameConj (hsame_trans data.right.right.right (hsame_symm sameYY'))
        exact Exists.intro s
          (And.intro data.left (And.intro centralX (And.intro centralY endpoint)))

theorem group_centralizer_normalizer_orbit_endpoint_transport_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y x' y' : BHist} :
    let Centralizer := fun q : BHist => hsame (mul q a) (mul a q)
    let Conj := fun s q : BHist => mul (mul s q) (inv s)
    let Normalizer := fun s : BHist =>
      (forall q : BHist, Centralizer q -> Centralizer (Conj s q)) ∧
        (forall q : BHist, Centralizer q -> Centralizer (Conj (inv s) q))
    let Orbit := fun p q : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer p ∧ Centralizer q ∧ hsame (Conj s p) q)
    Centralizer x -> Centralizer y -> Centralizer x' -> Centralizer y' ->
      hsame x x' -> hsame y y' -> (Orbit x y <-> Orbit x' y') := by
  exact BEDC.Derived.GroupUp.group_centralizer_normalizer_orbit_endpoint_transport_from_empty_unit_iff
    leftId rightId mulCongr
    (group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv)

end BEDC.Derived.GroupUp
