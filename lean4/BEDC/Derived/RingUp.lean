import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Derived.GroupUp
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.MonoidUp

def RingSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def RingSingletonClassifier (h k : BHist) : Prop :=
  RingSingletonCarrier h ∧ RingSingletonCarrier k ∧ hsame h k

def RingSingletonAdd (_x _y : BHist) : BHist :=
  BHist.Empty

def RingSingletonNeg (_x : BHist) : BHist :=
  BHist.Empty

def RingSingletonZero : BHist :=
  BHist.Empty

def RingSingletonMul (_x _y : BHist) : BHist :=
  BHist.Empty

def RingSingletonOne : BHist :=
  BHist.Empty

theorem RingSingletonEmptyHistory_laws :
    SemanticNameCert RingSingletonCarrier RingSingletonCarrier RingSingletonCarrier
        RingSingletonClassifier ∧
      (∀ {x y : BHist}, RingSingletonCarrier x → RingSingletonCarrier y →
        RingSingletonClassifier (RingSingletonAdd x y) RingSingletonZero) ∧
      (∀ {x : BHist}, RingSingletonCarrier x →
        RingSingletonClassifier (RingSingletonNeg x) RingSingletonZero) ∧
      (∀ {x y : BHist}, RingSingletonCarrier x → RingSingletonCarrier y →
        RingSingletonClassifier (RingSingletonMul x y) RingSingletonZero) ∧
      (∀ {x y z : BHist}, RingSingletonCarrier x → RingSingletonCarrier y →
        RingSingletonCarrier z →
          RingSingletonClassifier (RingSingletonMul x (RingSingletonAdd y z))
            (RingSingletonAdd (RingSingletonMul x y) (RingSingletonMul x z))) ∧
      (∀ {x y z : BHist}, RingSingletonCarrier x → RingSingletonCarrier y →
        RingSingletonCarrier z →
          RingSingletonClassifier (RingSingletonMul (RingSingletonAdd x y) z)
            (RingSingletonAdd (RingSingletonMul x z) (RingSingletonMul y z))) ∧
      (∀ {x : BHist}, RingSingletonCarrier x →
        RingSingletonClassifier (RingSingletonMul RingSingletonOne x) x) := by
  have emptyCarrier : RingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : RingSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro h k r sameHK sameKR
          exact And.intro sameHK.left
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
  · constructor
    · intro x y _carrierX _carrierY
      exact emptyClassified
    · constructor
      · intro x _carrierX
        exact emptyClassified
      · constructor
        · intro x y _carrierX _carrierY
          exact emptyClassified
        · constructor
          · intro x y z _carrierX _carrierY _carrierZ
            exact emptyClassified
          · constructor
            · intro x y z _carrierX _carrierY _carrierZ
              exact emptyClassified
            · intro x carrierX
              exact And.intro emptyCarrier (And.intro carrierX (hsame_symm carrierX))

theorem RingSingletonClassifier_append_visible_right_absurd {h p q : BHist} :
    (RingSingletonClassifier h (BEDC.FKernel.Cont.append p (BHist.e0 q)) -> False) ∧
      (RingSingletonClassifier h (BEDC.FKernel.Cont.append p (BHist.e1 q)) -> False) := by
  constructor
  · intro classified
    have emptyParts := BEDC.FKernel.Cont.append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right
  · intro classified
    have emptyParts := BEDC.FKernel.Cont.append_eq_empty_iff.mp classified.right.left
    cases emptyParts.right

theorem RingSingletonClassifier_append_visible_left_absurd {p q h : BHist} :
    (RingSingletonClassifier (append p (BHist.e0 q)) h -> False) ∧
      (RingSingletonClassifier (append p (BHist.e1 q)) h -> False) := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.left
    cases emptyParts.right

theorem RingSingletonClassifier_append_split_empty {p q h : BHist} :
    RingSingletonClassifier (append p q) h ↔
      RingSingletonCarrier p ∧ RingSingletonCarrier q ∧ RingSingletonCarrier h := by
  constructor
  · intro classified
    have split := append_eq_empty_iff.mp classified.left
    exact And.intro split.left (And.intro split.right classified.right.left)
  · intro data
    cases data with
    | intro carrierP rest =>
        cases rest with
        | intro carrierQ carrierH =>
            have appendCarrier : RingSingletonCarrier (append p q) :=
              append_eq_empty_iff.mpr (And.intro carrierP carrierQ)
            exact And.intro appendCarrier
              (And.intro carrierH (hsame_trans appendCarrier (hsame_symm carrierH)))

theorem concrete_singleton_history_ring_laws :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let add : BHist -> BHist -> BHist := append
    let neg : BHist -> BHist := fun _ => BHist.Empty
    let zero : BHist := BHist.Empty
    let mul : BHist -> BHist -> BHist := append
    let one : BHist := BHist.Empty
    Carrier zero ∧
      (∀ {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y)) ∧
      (∀ {x : BHist}, Carrier x -> Carrier (neg x)) ∧
      (∀ {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) ∧
      (∀ {x : BHist}, Carrier x -> Classifier (add zero x) x) ∧
      (∀ {x : BHist}, Carrier x -> Classifier (add x zero) x) ∧
      (∀ {x y z : BHist}, Carrier x -> Carrier y -> Carrier z ->
        Classifier (mul x (add y z)) (add (mul x y) (mul x z))) ∧
      (∀ {x y z : BHist}, Carrier x -> Carrier y -> Carrier z ->
        Classifier (mul (add x y) z) (add (mul x z) (mul y z))) := by
  dsimp
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro x y carrierX carrierY
      cases carrierX
      cases carrierY
      rfl
    · constructor
      · intro x _carrierX
        exact hsame_refl BHist.Empty
      · constructor
        · intro x y carrierX carrierY
          cases carrierX
          cases carrierY
          rfl
        · constructor
          · intro x carrierX
            cases carrierX
            exact And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
          · constructor
            · intro x carrierX
              cases carrierX
              exact And.intro (hsame_refl BHist.Empty)
                (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
            · constructor
              · intro x y z carrierX carrierY carrierZ
                cases carrierX
                cases carrierY
                cases carrierZ
                exact And.intro (hsame_refl BHist.Empty)
                  (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
              · intro x y z carrierX carrierY carrierZ
                cases carrierX
                cases carrierY
                cases carrierZ
                exact And.intro (hsame_refl BHist.Empty)
                  (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem ring_add_right_inverse {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero) :
    forall x : BHist, hsame (add x (neg x)) zero := by
  intro x
  exact hsame_trans (addComm x (neg x)) (negLeft x)

theorem ring_neg_zero {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero) :
    hsame (neg zero) zero := by
  exact hsame_trans (hsame_symm (zeroLeft (neg zero)))
    (hsame_trans (addComm zero (neg zero)) (negLeft zero))

theorem ring_add_duplicate_eq_zero {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b')) :
    forall a : BHist, hsame a (add a a) -> hsame a zero := by
  intro a duplicate
  have negStep : hsame (add (neg a) a) (add (neg a) (add a a)) := by
    exact addCongr (hsame_refl (neg a)) duplicate
  have assocBack : hsame (add (neg a) (add a a)) (add (add (neg a) a) a) := by
    exact hsame_symm (addAssoc (neg a) a a)
  have negToZeroAdd : hsame (add (add (neg a) a) a) (add zero a) := by
    exact addCongr (negLeft a) (hsame_refl a)
  have negToA : hsame (add (neg a) a) a := by
    exact hsame_trans negStep
      (hsame_trans assocBack (hsame_trans negToZeroAdd (zeroLeft a)))
  have zeroToA : hsame zero a := by
    exact hsame_trans (hsame_symm (negLeft a)) negToA
  exact hsame_symm zeroToA

theorem ring_add_duplicate_empty_iff {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    {a : BHist} :
    hsame a (add a a) <-> hsame a BHist.Empty := by
  constructor
  · intro duplicate
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr a duplicate
  · intro aEmpty
    have duplicateEmpty : hsame (add a a) (add BHist.Empty BHist.Empty) :=
      addCongr aEmpty aEmpty
    have emptySum : hsame (add a a) BHist.Empty :=
      hsame_trans duplicateEmpty (zeroLeft BHist.Empty)
    exact hsame_trans aEmpty (hsame_symm emptySum)

theorem ring_add_right_zero {add : BHist -> BHist -> BHist} {zero : BHist}
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x) :
    forall x : BHist, hsame (add x zero) x := by
  intro x
  exact hsame_trans (addComm x zero) (zeroLeft x)

theorem ring_mul_zero_absorption {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    And (forall x : BHist, hsame (mul x zero) zero)
      (forall x : BHist, hsame (mul zero x) zero) := by
  constructor
  · intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul x (add zero zero)) (mul x zero) := by
      exact mulCongr (hsame_refl x) zeroZero
    have distrib : hsame (mul x (add zero zero)) (add (mul x zero) (mul x zero)) := by
      exact leftDistrib x zero zero
    have duplicate : hsame (mul x zero) (add (mul x zero) (mul x zero)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul x zero) duplicate
  · intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul (add zero zero) x) (mul zero x) := by
      exact mulCongr zeroZero (hsame_refl x)
    have distrib : hsame (mul (add zero zero) x) (add (mul zero x) (mul zero x)) := by
      exact rightDistrib zero zero x
    have duplicate : hsame (mul zero x) (add (mul zero x) (mul zero x)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul zero x) duplicate

theorem ring_mul_neg_left_inverse_sum_zero {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (add (mul (neg x) y) (mul x y)) zero := by
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have distrib :
      hsame (mul (add (neg x) x) y) (add (mul (neg x) y) (mul x y)) := by
    exact rightDistrib (neg x) x y
  have inverseProduct : hsame (mul (add (neg x) x) y) (mul zero y) := by
    exact mulCongr (negLeft x) (hsame_refl y)
  exact hsame_trans (hsame_symm distrib)
    (hsame_trans inverseProduct (zeroAbsorption.right y))

theorem ring_mul_neg_right_inverse_sum_zero {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (add (mul x (neg y)) (mul x y)) zero := by
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have distrib :
      hsame (mul x (add (neg y) y)) (add (mul x (neg y)) (mul x y)) := by
    exact leftDistrib x (neg y) y
  have inverseProduct : hsame (mul x (add (neg y) y)) (mul x zero) := by
    exact mulCongr (hsame_refl x) (negLeft y)
  exact hsame_trans (hsame_symm distrib)
    (hsame_trans inverseProduct (zeroAbsorption.left x))

theorem ring_mul_neg_left_right_same {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul (neg x) y) (mul x (neg y)) := by
  have addRightZero : forall x : BHist, hsame (add x zero) x := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) zero := by
    exact ring_add_right_inverse addComm negLeft
  have leftNegative :
      forall x y : BHist, hsame (add (mul (neg x) y) (mul x y)) zero := by
    exact ring_mul_neg_left_inverse_sum_zero addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  have rightNegative :
      forall x y : BHist, hsame (add (mul x (neg y)) (mul x y)) zero := by
    exact ring_mul_neg_right_inverse_sum_zero addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  intro x y
  have sameProducts :
      hsame (add (mul (neg x) y) (mul x y)) (add (mul x (neg y)) (mul x y)) := by
    exact hsame_trans (leftNegative x y) (hsame_symm (rightNegative x y))
  exact BEDC.Derived.GroupUp.group_right_cancel addAssoc addRightZero addCongr addRightInverse
    sameProducts

theorem ring_mul_neg_left_eq_neg_mul {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul (neg x) y) (neg (mul x y)) := by
  intro x y
  have addRightZero : forall z : BHist, hsame (add z zero) z := by
    exact ring_add_right_zero addComm zeroLeft
  have leftSum :
      hsame (add (mul (neg x) y) (mul x y)) zero := by
    exact ring_mul_neg_left_inverse_sum_zero addAssoc zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib x y
  have rightSum :
      hsame (add (mul x y) (neg (mul x y))) zero := by
    exact ring_add_right_inverse addComm negLeft (mul x y)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    addAssoc
    zeroLeft
    addRightZero
    addCongr
    leftSum
    rightSum

theorem ring_mul_neg_right_eq_neg_mul {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul x (neg y)) (neg (mul x y)) := by
  intro x y
  have addRightZero : forall z : BHist, hsame (add z zero) z := by
    exact ring_add_right_zero addComm zeroLeft
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  have leftSum :
      hsame (add (mul x (neg y)) (mul x y)) zero := by
    have distrib :
        hsame (mul x (add (neg y) y)) (add (mul x (neg y)) (mul x y)) := by
      exact leftDistrib x (neg y) y
    have inverseProduct : hsame (mul x (add (neg y) y)) (mul x zero) := by
      exact mulCongr (hsame_refl x) (negLeft y)
    exact hsame_trans (hsame_symm distrib)
      (hsame_trans inverseProduct (zeroAbsorption.left x))
  have rightSum :
      hsame (add (mul x y) (neg (mul x y))) zero := by
    exact ring_add_right_inverse addComm negLeft (mul x y)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    addAssoc
    zeroLeft
    addRightZero
    addCongr
    leftSum
    rightSum

theorem ring_mul_neg_neg_eq_mul {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y : BHist, hsame (mul (neg x) (neg y)) (mul x y) := by
  have addRightZero : forall z : BHist, hsame (add z zero) z := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall z : BHist, hsame (add z (neg z)) zero := by
    exact ring_add_right_inverse addComm negLeft
  have negCongr : forall {u v : BHist}, hsame u v -> hsame (neg u) (neg v) := by
    exact BEDC.Derived.GroupUp.group_inverse_congruence_from_laws
      addAssoc zeroLeft addRightZero addCongr negLeft addRightInverse
  have negInvolutive : forall z : BHist, hsame (neg (neg z)) z := by
    exact BEDC.Derived.GroupUp.group_left_inverse_involutive
      addAssoc zeroLeft addRightZero addCongr negLeft
  intro x y
  have leftProduct : hsame (mul (neg x) (neg y)) (neg (mul x (neg y))) := by
    exact ring_mul_neg_left_eq_neg_mul addAssoc addComm zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib x (neg y)
  have rightProduct : hsame (mul x (neg y)) (neg (mul x y)) := by
    exact ring_mul_neg_right_eq_neg_mul addAssoc addComm zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib x y
  exact hsame_trans leftProduct
    (hsame_trans (negCongr rightProduct) (negInvolutive (mul x y)))

theorem ring_stability_certificate_fields {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist} {zero one : BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add zero x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) zero)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (oneLeft : forall x : BHist, hsame (mul one x) x)
    (oneRight : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    ((forall x : BHist, MonoidClassifierSpec hsame x x) /\
      (forall {x y z : BHist}, MonoidClassifierSpec hsame x y ->
        MonoidClassifierSpec hsame y z ->
          MonoidClassifierSpec hsame x z) /\
      (forall x y z : BHist,
        MonoidClassifierSpec hsame (mul (mul x y) z) (mul x (mul y z))) /\
      (forall x : BHist, MonoidClassifierSpec hsame (mul one x) x) /\
      (forall x : BHist, MonoidClassifierSpec hsame (mul x one) x) /\
      (forall {a a' b b' : BHist}, MonoidClassifierSpec hsame a a' ->
        MonoidClassifierSpec hsame b b' ->
          MonoidClassifierSpec hsame (mul a b) (mul a' b'))) /\
      (forall x y z : BHist, hsame (add (add x y) z) (add x (add y z))) /\
      (forall x y : BHist, hsame (add x y) (add y x)) /\
      (forall x : BHist, hsame (add zero x) x) /\
      (forall x : BHist, hsame (add x zero) x) /\
      (forall x : BHist, hsame (add (neg x) x) zero) /\
      (forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
        hsame (add a b) (add a' b')) /\
      (forall x y z : BHist, hsame (mul x (add y z)) (add (mul x y) (mul x z))) /\
      (forall x y z : BHist, hsame (mul (add x y) z) (add (mul x z) (mul y z))) /\
      (forall x : BHist, hsame (mul x zero) zero) /\
      (forall x : BHist, hsame (mul zero x) zero) := by
  have addRightZero : forall x : BHist, hsame (add x zero) x := by
    intro x
    exact hsame_trans (addComm x zero) (zeroLeft x)
  have mulZeroRight : forall x : BHist, hsame (mul x zero) zero := by
    intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul x (add zero zero)) (mul x zero) := by
      exact mulCongr (hsame_refl x) zeroZero
    have distrib : hsame (mul x (add zero zero)) (add (mul x zero) (mul x zero)) := by
      exact leftDistrib x zero zero
    have duplicate : hsame (mul x zero) (add (mul x zero) (mul x zero)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul x zero) duplicate
  have mulZeroLeft : forall x : BHist, hsame (mul zero x) zero := by
    intro x
    have zeroZero : hsame (add zero zero) zero := by
      exact zeroLeft zero
    have sameLeft : hsame (mul (add zero zero) x) (mul zero x) := by
      exact mulCongr zeroZero (hsame_refl x)
    have distrib : hsame (mul (add zero zero) x) (add (mul zero x) (mul zero x)) := by
      exact rightDistrib zero zero x
    have duplicate : hsame (mul zero x) (add (mul zero x) (mul zero x)) := by
      exact hsame_trans (hsame_symm sameLeft) distrib
    exact ring_add_duplicate_eq_zero addAssoc zeroLeft negLeft addCongr (mul zero x) duplicate
  constructor
  · exact monoid_stability_certificate_fields
      hsame_refl
      hsame_trans
      mulAssoc
      oneLeft
      oneRight
      mulCongr
  · constructor
    · exact addAssoc
    · constructor
      · exact addComm
      · constructor
        · exact zeroLeft
        · constructor
          · exact addRightZero
          · constructor
            · exact negLeft
            · constructor
              · intro a a' b b' sameA sameB
                exact addCongr sameA sameB
              · constructor
                · exact leftDistrib
                · constructor
                  · exact rightDistrib
                  · constructor
                    · exact mulZeroRight
                    · exact mulZeroLeft

end BEDC.Derived.RingUp
