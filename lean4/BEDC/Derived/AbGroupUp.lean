import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.Derived.GroupUp
import BEDC.Derived.GroupUp.Commutator
import BEDC.Derived.GroupUp.CentralizerNormalizer

namespace BEDC.Derived.AbGroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem concrete_singleton_history_abgroup_laws :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let mul : BHist -> BHist -> BHist := BEDC.FKernel.Cont.append
    Carrier BHist.Empty ∧
      (forall {h k : BHist}, Carrier h -> Carrier k -> Carrier (mul h k)) ∧
      (forall {h k : BHist}, Carrier h -> Carrier k ->
        Classifier (mul h k) (mul k h)) := by
  dsimp
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro h k carrierH carrierK
      cases carrierH
      cases carrierK
      exact hsame_refl BHist.Empty
    · intro h k carrierH carrierK
      cases carrierH
      cases carrierK
      exact And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem singleton_empty_history_abgroup_laws :
    SemanticNameCert BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonClassifier ∧
      (∀ {x y : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier x ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier y ->
          BEDC.Derived.GroupUp.GroupSingletonCarrier BHist.Empty) ∧
      (∀ {x : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier x ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier BHist.Empty) ∧
      (∀ {x : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier x ->
        BEDC.Derived.GroupUp.GroupSingletonClassifier BHist.Empty x) ∧
      (∀ {x y : BHist}, BEDC.Derived.GroupUp.GroupSingletonCarrier x ->
        BEDC.Derived.GroupUp.GroupSingletonCarrier y ->
          BEDC.Derived.GroupUp.GroupSingletonClassifier BHist.Empty BHist.Empty) := by
  have laws := BEDC.Derived.GroupUp.GroupSingletonHistory_laws
  have semantic :
      SemanticNameCert BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonCarrier
        BEDC.Derived.GroupUp.GroupSingletonClassifier := laws.left
  have emptyCarrier : BEDC.Derived.GroupUp.GroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyClassified :
      BEDC.Derived.GroupUp.GroupSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact semantic
  · constructor
    · intro _x _y _carrierX _carrierY
      exact emptyCarrier
    · constructor
      · intro _x _carrierX
        exact emptyCarrier
      · constructor
        · intro x carrierX
          exact And.intro emptyCarrier (And.intro carrierX (hsame_symm carrierX))
        · intro _x _y _carrierX _carrierY
          exact emptyClassified

theorem abgroup_mul_left_right_swap {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul a (mul b c)) (mul b (mul a c)) := by
  intro a b c
  exact hsame_trans (hsame_symm (assocC a b c))
    (hsame_trans (mulCongr (commC a b) (hsame_refl c)) (assocC b a c))

theorem abgroup_mul_middle_four {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c d : BHist,
      hsame (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
  intro a b c d
  have reassocLeft :
      hsame (mul (mul a b) (mul c d)) (mul a (mul b (mul c d))) := by
    exact assocC a b (mul c d)
  have swapRight : hsame (mul b (mul c d)) (mul c (mul b d)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr b c d
  have transportRight :
      hsame (mul a (mul b (mul c d))) (mul a (mul c (mul b d))) := by
    exact mulCongr (hsame_refl a) swapRight
  have reassocRight :
      hsame (mul a (mul c (mul b d))) (mul (mul a c) (mul b d)) := by
    exact hsame_symm (assocC a c (mul b d))
  exact hsame_trans reassocLeft (hsame_trans transportRight reassocRight)

theorem abgroup_mul_inverse_pair_collapse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall a b : BHist, hsame (mul (mul a b) (mul (inv a) (inv b))) e := by
  intro a b
  have regroup :
      hsame (mul (mul a b) (mul (inv a) (inv b)))
        (mul (mul a (inv a)) (mul b (inv b))) := by
    exact abgroup_mul_middle_four assocC commC mulCongr a b (inv a) (inv b)
  have collapseFactors :
      hsame (mul (mul a (inv a)) (mul b (inv b))) (mul e e) := by
    exact mulCongr (rightInv a) (rightInv b)
  exact hsame_trans regroup (hsame_trans collapseFactors (rightId e))

theorem abgroup_conjugation_collapse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall a b : BHist, hsame (mul a (mul b (inv a))) b := by
  intro a b
  have swap :
      hsame (mul a (mul b (inv a))) (mul b (mul a (inv a))) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr a b (inv a)
  have collapseInner : hsame (mul b (mul a (inv a))) (mul b e) := by
    exact mulCongr (hsame_refl b) (rightInv a)
  exact hsame_trans swap (hsame_trans collapseInner (rightId b))

theorem abgroup_inverse_conjugation_collapse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e) :
    forall a b : BHist, hsame (mul (inv a) (mul b a)) b := by
  intro a b
  have swap :
      hsame (mul (inv a) (mul b a)) (mul b (mul (inv a) a)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr (inv a) b a
  have collapseInner : hsame (mul b (mul (inv a) a)) (mul b e) := by
    exact mulCongr (hsame_refl b) (leftInv a)
  exact hsame_trans swap (hsame_trans collapseInner (rightId b))

theorem abgroup_centralizer_commutator_collapse {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty) {a x : BHist} :
    hsame (mul x a) (mul a x) ∧
      hsame (mul (mul x a) (mul (inv x) (inv a))) BHist.Empty ∧
      hsame (mul a (mul x (inv a))) x := by
  have central : hsame (mul x a) (mul a x) := commC x a
  have commutator :
      hsame (mul (mul x a) (mul (inv x) (inv a))) BHist.Empty := by
    exact (BEDC.Derived.GroupUp.group_commutator_trivial_iff_commutes_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv).mpr central
  have conjugation : hsame (mul a (mul x (inv a))) x := by
    exact abgroup_conjugation_collapse assocC commC rightId mulCongr rightInv a x
  exact And.intro central (And.intro commutator conjugation)

theorem abgroup_centralizer_normalizer_orbit_collapse_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    let Centralizer := fun q : BHist => hsame (mul q a) (mul a q)
    let Conj := fun s q : BHist => mul (mul s q) (inv s)
    let Normalizer := fun s : BHist =>
      (forall q : BHist, Centralizer q -> Centralizer (Conj s q)) ∧
        (forall q : BHist, Centralizer q -> Centralizer (Conj (inv s) q))
    let Orbit := fun p q : BHist =>
      Exists (fun s : BHist =>
        Normalizer s ∧ Centralizer p ∧ Centralizer q ∧ hsame (Conj s p) q)
    Centralizer x -> Centralizer y -> (Orbit x y <-> hsame x y) := by
  dsimp
  intro centralX centralY
  constructor
  · intro orbitXY
    cases orbitXY with
    | intro s data =>
        have reassoc :
            hsame (mul (mul s x) (inv s)) (mul s (mul x (inv s))) :=
          assocC s x (inv s)
        have collapse :
            hsame (mul s (mul x (inv s))) x :=
          abgroup_conjugation_collapse (mul := mul) (e := BHist.Empty) (inv := inv)
            assocC commC rightId mulCongr rightInv s x
        have fixedConj : hsame (mul (mul s x) (inv s)) x :=
          hsame_trans reassoc collapse
        exact hsame_trans (hsame_symm fixedConj) data.right.right.right
  · intro sameXY
    exact BEDC.Derived.GroupUp.group_centralizer_normalizer_orbit_hsame_lift_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralX centralY sameXY

theorem abgroup_centralizer_normalizer_orbit_fiber_determinacy_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
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
      Orbit x y -> Orbit x z -> hsame y z := by
  dsimp
  intro centralX centralY centralZ orbitXY orbitXZ
  have collapseXY :=
    abgroup_centralizer_normalizer_orbit_collapse_from_empty_unit
      assocC leftId rightId commC mulCongr leftInv rightInv
      (a := a) (x := x) (y := y) centralX centralY
  have collapseXZ :=
    abgroup_centralizer_normalizer_orbit_collapse_from_empty_unit
      assocC leftId rightId commC mulCongr leftInv rightInv
      (a := a) (x := x) (y := z) centralX centralZ
  have sameXY : hsame x y := Iff.mp collapseXY orbitXY
  have sameXZ : hsame x z := Iff.mp collapseXZ orbitXZ
  exact hsame_trans (hsame_symm sameXY) sameXZ

theorem abgroup_centralizer_normalizer_collapse
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a s x : BHist} :
    let Centralizer := fun y : BHist => hsame (mul y a) (mul a y)
    let Conj := fun t y : BHist => mul (mul t y) (inv t)
    let Normalizer := fun t : BHist =>
      (forall y : BHist, Centralizer y -> Centralizer (Conj t y)) ∧
        (forall y : BHist, Centralizer y -> Centralizer (Conj (inv t) y))
    Centralizer x ->
      Normalizer s ∧ Centralizer (Conj s x) ∧ hsame (Conj s x) x := by
  dsimp
  intro _centralX
  have totalCentral :
      forall y : BHist, hsame (mul y a) (mul a y) := by
    intro y
    exact (abgroup_centralizer_commutator_collapse
      assocC leftId rightId commC mulCongr leftInv rightInv (a := a) (x := y)).left
  have normalizerS :
      (forall y : BHist, hsame (mul y a) (mul a y) ->
        hsame (mul (mul (mul s y) (inv s)) a)
          (mul a (mul (mul s y) (inv s)))) ∧
      (forall y : BHist, hsame (mul y a) (mul a y) ->
        hsame (mul (mul (mul (inv s) y) (inv (inv s))) a)
          (mul a (mul (mul (inv s) y) (inv (inv s))))) := by
    constructor
    · intro y _centralY
      exact totalCentral (mul (mul s y) (inv s))
    · intro y _centralY
      exact totalCentral (mul (mul (inv s) y) (inv (inv s)))
  have centralConj : hsame (mul (mul (mul s x) (inv s)) a)
      (mul a (mul (mul s x) (inv s))) :=
    totalCentral (mul (mul s x) (inv s))
  have collapseConj : hsame (mul (mul s x) (inv s)) x := by
    exact hsame_trans (assocC s x (inv s))
      (abgroup_conjugation_collapse assocC commC rightId mulCongr rightInv s x)
  exact And.intro normalizerS (And.intro centralConj collapseConj)

theorem abgroup_inverse_mul {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall x y : BHist, hsame (inv (mul x y)) (mul (inv x) (inv y)) := by
  intro x y
  exact hsame_trans
    (BEDC.Derived.GroupUp.group_inverse_mul_reverse assocC leftId rightId mulCongr
      leftInv rightInv x y)
    (commC (inv y) (inv x))

theorem abgroup_mul_right_factor_swap {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul a b) c) (mul (mul a c) b) := by
  intro a b c
  exact hsame_trans (assocC a b c)
    (hsame_trans (mulCongr (hsame_refl a) (commC b c)) (hsame_symm (assocC a c b)))

theorem abgroup_mul_common_left_factor_collect {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul a b) (mul a c)) (mul a (mul a (mul b c))) := by
  intro a b c
  have reassoc :
      hsame (mul (mul a b) (mul a c)) (mul a (mul b (mul a c))) := by
    exact assocC a b (mul a c)
  have collectTail : hsame (mul b (mul a c)) (mul a (mul b c)) := by
    exact abgroup_mul_left_right_swap assocC commC mulCongr b a c
  have transportTail :
      hsame (mul a (mul b (mul a c))) (mul a (mul a (mul b c))) := by
    exact mulCongr (hsame_refl a) collectTail
  exact hsame_trans reassoc transportTail

theorem abgroup_mul_common_right_factor_collect {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b')) :
    forall a b c : BHist, hsame (mul (mul b a) (mul c a))
      (mul a (mul a (mul b c))) := by
  intro a b c
  have exposeLeftFactors :
      hsame (mul (mul b a) (mul c a)) (mul (mul a b) (mul a c)) := by
    exact mulCongr (commC b a) (commC c a)
  have collect :
      hsame (mul (mul a b) (mul a c)) (mul a (mul a (mul b c))) := by
    exact abgroup_mul_common_left_factor_collect assocC commC mulCongr a b c
  exact hsame_trans exposeLeftFactors collect

theorem abgroup_mul_balanced_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b c : BHist} :
    hsame (mul a b) (mul c a) -> hsame b c := by
  intro sameBalanced
  exact BEDC.Derived.GroupUp.group_left_cancel assocC leftId mulCongr leftInv
    (hsame_trans sameBalanced (commC c a))

protected theorem abgroup_mul_middle_four_double_cancel_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b c d u : BHist} :
    hsame (mul (mul a b) (mul c d)) (mul (mul a c) (mul u d)) ->
      hsame b u := by
  intro sameProducts
  have middle :
      hsame (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
    exact abgroup_mul_middle_four assocC commC mulCongr a b c d
  have sameTails :
      hsame (mul (mul a c) (mul b d)) (mul (mul a c) (mul u d)) :=
    hsame_trans (hsame_symm middle) sameProducts
  have cancelLeft : hsame (mul b d) (mul u d) := by
    exact BEDC.Derived.GroupUp.group_left_cancel assocC leftId mulCongr leftInv
      sameTails
  exact BEDC.Derived.GroupUp.group_right_cancel assocC rightId mulCongr rightInv
    cancelLeft

protected theorem abgroup_mul_middle_four_transported_double_cancel_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (commC : forall x y : BHist, hsame (mul x y) (mul y x))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b c d u v : BHist} :
    hsame (mul (mul a b) (mul c d)) (mul (mul a u) (mul c v)) ->
      hsame d v -> hsame b u := by
  intro sameProducts sameDV
  have middleLeft :
      hsame (mul (mul a b) (mul c d)) (mul (mul a c) (mul b d)) := by
    exact abgroup_mul_middle_four assocC commC mulCongr a b c d
  have middleRight :
      hsame (mul (mul a u) (mul c v)) (mul (mul a c) (mul u v)) := by
    exact abgroup_mul_middle_four assocC commC mulCongr a u c v
  have sameAligned :
      hsame (mul (mul a c) (mul b d)) (mul (mul a c) (mul u v)) :=
    hsame_trans (hsame_symm middleLeft) (hsame_trans sameProducts middleRight)
  have sameTransported :
      hsame (mul (mul a c) (mul u v)) (mul (mul a c) (mul u d)) := by
    exact mulCongr (hsame_refl (mul a c)) (mulCongr (hsame_refl u) (hsame_symm sameDV))
  have sameTails : hsame (mul b d) (mul u d) := by
    exact BEDC.Derived.GroupUp.group_left_cancel assocC leftId mulCongr leftInv
      (hsame_trans sameAligned sameTransported)
  exact BEDC.Derived.GroupUp.group_right_cancel assocC rightId mulCongr rightInv
    sameTails

theorem history_append_nonempty_left_ne_right :
    (forall {h k : BHist}, append (BHist.e0 h) k = k -> False) ∧
      (forall {h k : BHist}, append (BHist.e1 h) k = k -> False) := by
  constructor
  · intro h k same
    induction k generalizing h with
    | Empty =>
        cases same
    | e0 k ih =>
        exact ih (BHist.e0.inj same)
    | e1 k ih =>
        exact ih (BHist.e1.inj same)
  · intro h k same
    induction k generalizing h with
    | Empty =>
        cases same
    | e0 k ih =>
        exact ih (BHist.e0.inj same)
    | e1 k ih =>
        exact ih (BHist.e1.inj same)

end BEDC.Derived.AbGroupUp
