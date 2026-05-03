import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_normalizer_conjugation_inverse_roundtrip_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s x : BHist} :
    let Centralizer := fun y : BHist => hsame (mul y a) (mul a y)
    let Conj := fun u y : BHist => mul (mul u y) (inv u)
    let Normalizer := fun u : BHist =>
      (forall y : BHist, Centralizer y -> Centralizer (Conj u y)) ∧
        (forall y : BHist, Centralizer y -> Centralizer (Conj (inv u) y))
    Normalizer s -> Centralizer x ->
      Centralizer (Conj s x) ∧ Centralizer (Conj (inv s) x) ∧
        hsame (Conj (inv s) (Conj s x)) x ∧
          hsame (Conj s (Conj (inv s) x)) x := by
  dsimp
  intro normS centralX
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
          (mul (mul u (mul v y)) (inv (mul u v))) :=
      mulCongr (assocC u v y) (hsame_refl (inv (mul u v)))
    have replaceInv :
        hsame (mul (mul u (mul v y)) (inv (mul u v)))
          (mul (mul u (mul v y)) (mul (inv v) (inv u))) :=
      mulCongr (hsame_refl (mul u (mul v y))) reverseInv
    have reassocTail :
        hsame (mul (mul u (mul v y)) (mul (inv v) (inv u)))
          (mul (mul (mul u (mul v y)) (inv v)) (inv u)) :=
      hsame_symm (assocC (mul u (mul v y)) (inv v) (inv u))
    have reassocMiddle :
        hsame (mul (mul (mul u (mul v y)) (inv v)) (inv u))
          (mul (mul u (mul (mul v y) (inv v))) (inv u)) :=
      mulCongr (assocC u (mul v y) (inv v)) (hsame_refl (inv u))
    exact hsame_trans reassocHead
      (hsame_trans replaceInv (hsame_trans reassocTail reassocMiddle))
  have unitAction : forall q : BHist,
      hsame (mul (mul BHist.Empty q) (inv BHist.Empty)) q := by
    intro q
    have invEmpty : hsame (inv BHist.Empty) BHist.Empty :=
      group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
    exact hsame_trans (mulCongr (leftId q) invEmpty) (rightId q)
  have inverseAction : forall u q : BHist,
      hsame (mul (mul (inv u) (mul (mul u q) (inv u))) (inv (inv u))) q := by
    intro u q
    have comp :
        hsame (mul (mul (mul (inv u) u) q) (inv (mul (inv u) u)))
          (mul (mul (inv u) (mul (mul u q) (inv u))) (inv (inv u))) :=
      conjCompose (inv u) u q
    have sameUnitHead :
        hsame (mul (mul (mul (inv u) u) q) (inv (mul (inv u) u)))
          (mul (mul BHist.Empty q) (inv BHist.Empty)) :=
      conjCongrLeft (leftInv u)
    exact hsame_trans (hsame_symm comp) (hsame_trans sameUnitHead (unitAction q))
  have invInvS : hsame (inv (inv s)) s :=
    group_left_inverse_involutive assocC leftId rightId mulCongr leftInv s
  have secondRoundtrip :
      hsame (mul (mul s (mul (mul (inv s) x) (inv (inv s)))) (inv s)) x := by
    have sameHead :
        hsame (mul (mul s (mul (mul (inv s) x) (inv (inv s)))) (inv s))
          (mul (mul (inv (inv s)) (mul (mul (inv s) x) (inv (inv s))))
            (inv (inv (inv s)))) :=
      hsame_symm (conjCongrLeft invInvS)
    exact hsame_trans sameHead (inverseAction (inv s) x)
  exact And.intro (normS.left x centralX)
    (And.intro (normS.right x centralX)
      (And.intro (inverseAction s x) secondRoundtrip))

protected theorem group_center_normalizer_orbit_collapse_from_empty_unit_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    let Center := fun z : BHist => forall q : BHist, hsame (mul z q) (mul q z)
    let Centralizer := fun z : BHist => hsame (mul z a) (mul a z)
    let Conj := fun s z : BHist => mul (mul s z) (inv s)
    let Normalizer := fun s : BHist =>
      (forall z : BHist, Centralizer z -> Centralizer (Conj s z)) ∧
        (forall z : BHist, Centralizer z -> Centralizer (Conj (inv s) z))
    let Orbit := fun p q : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer p ∧ Centralizer q ∧ hsame (Conj s p) q)
    Center x -> Centralizer y -> (Orbit x y <-> hsame x y) := by
  dsimp
  intro centerX centralY
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
  have unitAction : forall q : BHist,
      hsame (mul (mul BHist.Empty q) (inv BHist.Empty)) q := by
    intro q
    have invEmpty : hsame (inv BHist.Empty) BHist.Empty :=
      group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
    exact hsame_trans (mulCongr (leftId q) invEmpty) (rightId q)
  have centerConjFixed : forall s q : BHist,
      (forall r : BHist, hsame (mul q r) (mul r q)) ->
        hsame (mul (mul s q) (inv s)) q := by
    intro s q centerQ
    have reassocHead :
        hsame (mul (mul s q) (inv s)) (mul s (mul q (inv s))) :=
      assocC s q (inv s)
    have commuteTail :
        hsame (mul s (mul q (inv s))) (mul s (mul (inv s) q)) :=
      mulCongr (hsame_refl s) (centerQ (inv s))
    have reassocTail :
        hsame (mul s (mul (inv s) q)) (mul (mul s (inv s)) q) :=
      hsame_symm (assocC s (inv s) q)
    have collapseHead : hsame (mul (mul s (inv s)) q) (mul BHist.Empty q) :=
      mulCongr (rightInv s) (hsame_refl q)
    exact hsame_trans reassocHead
      (hsame_trans commuteTail
        (hsame_trans reassocTail (hsame_trans collapseHead (leftId q))))
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
  constructor
  · intro orbitXY
    cases orbitXY with
    | intro s data =>
        have fixedX : hsame (mul (mul s x) (inv s)) x := centerConjFixed s x centerX
        exact hsame_trans (hsame_symm fixedX) data.right.right.right
  · intro sameXY
    exact Exists.intro BHist.Empty
      (And.intro emptyNormalizer
        (And.intro (centerX a)
          (And.intro centralY (hsame_trans (unitAction x) sameXY))))

protected theorem group_center_normalizer_orbit_fiber_determinacy_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y z : BHist} :
    let Center := fun t : BHist => forall q : BHist, hsame (mul t q) (mul q t)
    let Centralizer := fun t : BHist => hsame (mul t a) (mul a t)
    let Conj := fun s t : BHist => mul (mul s t) (inv s)
    let Normalizer := fun s : BHist =>
      (forall t : BHist, Centralizer t -> Centralizer (Conj s t)) ∧
        (forall t : BHist, Centralizer t -> Centralizer (Conj (inv s) t))
    let Orbit := fun u v : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer u ∧ Centralizer v ∧ hsame (Conj s u) v)
    Center x -> Centralizer y -> Centralizer z -> Orbit x y -> Orbit x z -> hsame y z := by
  dsimp
  intro centerX centralY centralZ orbitXY orbitXZ
  have collapseY :=
    BEDC.Derived.GroupUp.group_center_normalizer_orbit_collapse_from_empty_unit_iff
      assocC leftId rightId mulCongr leftInv rightInv (a := a) (x := x) (y := y)
  have collapseZ :=
    BEDC.Derived.GroupUp.group_center_normalizer_orbit_collapse_from_empty_unit_iff
      assocC leftId rightId mulCongr leftInv rightInv (a := a) (x := x) (y := z)
  have sameXY : hsame x y := (collapseY centerX centralY).mp orbitXY
  have sameXZ : hsame x z := (collapseZ centerX centralZ).mp orbitXZ
  exact hsame_trans (hsame_symm sameXY) sameXZ

end BEDC.Derived.GroupUp
