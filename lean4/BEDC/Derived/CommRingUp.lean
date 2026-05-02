import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.RingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def CommRingSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def CommRingSingletonClassifier (h k : BHist) : Prop :=
  CommRingSingletonCarrier h ∧ CommRingSingletonCarrier k ∧ hsame h k

def CommRingSingletonAdd (_x _y : BHist) : BHist :=
  BHist.Empty

def CommRingSingletonNeg (_x : BHist) : BHist :=
  BHist.Empty

def CommRingSingletonZero : BHist :=
  BHist.Empty

def CommRingSingletonMul (_x _y : BHist) : BHist :=
  BHist.Empty

def CommRingSingletonOne : BHist :=
  BHist.Empty

theorem singleton_empty_history_commring_laws :
    SemanticNameCert CommRingSingletonCarrier CommRingSingletonCarrier
      CommRingSingletonCarrier CommRingSingletonClassifier ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x → CommRingSingletonCarrier y →
        CommRingSingletonClassifier (CommRingSingletonAdd x y) BHist.Empty) ∧
      (∀ {x : BHist}, CommRingSingletonCarrier x →
        CommRingSingletonClassifier (CommRingSingletonNeg x) BHist.Empty) ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x → CommRingSingletonCarrier y →
        CommRingSingletonClassifier (CommRingSingletonMul x y) BHist.Empty) ∧
      (∀ {x y : BHist}, CommRingSingletonCarrier x → CommRingSingletonCarrier y →
        CommRingSingletonClassifier (CommRingSingletonMul x y) (CommRingSingletonMul y x)) ∧
      (∀ {x y z : BHist}, CommRingSingletonCarrier x → CommRingSingletonCarrier y →
        CommRingSingletonCarrier z →
          CommRingSingletonClassifier (CommRingSingletonMul x (CommRingSingletonAdd y z))
            (CommRingSingletonAdd (CommRingSingletonMul x y) (CommRingSingletonMul x z))) ∧
      (∀ {x y z : BHist}, CommRingSingletonCarrier x → CommRingSingletonCarrier y →
        CommRingSingletonCarrier z →
          CommRingSingletonClassifier (CommRingSingletonMul (CommRingSingletonAdd x y) z)
            (CommRingSingletonAdd (CommRingSingletonMul x z) (CommRingSingletonMul y z))) ∧
      (∀ {x : BHist}, CommRingSingletonCarrier x →
        CommRingSingletonClassifier (CommRingSingletonMul CommRingSingletonOne x) x) := by
  have emptyCarrier : CommRingSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : CommRingSingletonClassifier BHist.Empty BHist.Empty :=
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

theorem commring_right_distrib_from_left {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z))) :
    forall x y z : BHist, hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
  intro x y z
  exact hsame_trans (mulComm (add x y) z)
    (hsame_trans (leftDistrib z x y)
      (addCongr (mulComm z x) (mulComm z y)))

 theorem commring_left_distrib_from_right {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall x y z : BHist, hsame (mul x (add y z)) (add (mul x y) (mul x z)) := by
  intro x y z
  exact hsame_trans (mulComm x (add y z))
    (hsame_trans (rightDistrib y z x)
      (addCongr (mulComm y x) (mulComm z x)))

theorem commring_square_add_expand {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall a b : BHist,
      hsame (mul (add a b) (add a b))
        (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))) := by
  intro a b
  have outer :
      hsame (mul (add a b) (add a b))
        (add (mul a (add a b)) (mul b (add a b))) := by
    exact rightDistrib a b (add a b)
  have expandLeft :
      hsame (add (mul a (add a b)) (mul b (add a b)))
        (add (add (mul a a) (mul a b)) (add (mul b a) (mul b b))) := by
    exact addCongr (leftDistrib a a b) (leftDistrib b a b)
  have alignMiddle :
      hsame (add (add (mul a a) (mul a b)) (add (mul b a) (mul b b)))
        (add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))) := by
    exact addCongr (hsame_refl (add (mul a a) (mul a b)))
      (addCongr (mulComm b a) (hsame_refl (mul b b)))
  exact hsame_trans outer (hsame_trans expandLeft alignMiddle)

theorem commring_mul_add_add_expand {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z))) :
    forall a b c d : BHist,
      hsame (mul (add a b) (add c d))
        (add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))) := by
  intro a b c d
  have outer :
      hsame (mul (add a b) (add c d))
        (add (mul a (add c d)) (mul b (add c d))) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib a b (add c d)
  have inner :
      hsame (add (mul a (add c d)) (mul b (add c d)))
        (add (add (mul a c) (mul a d)) (add (mul b c) (mul b d))) := by
    exact addCongr (leftDistrib a c d) (leftDistrib b c d)
  exact hsame_trans outer inner

theorem commring_left_distrib_commuted_terms {add mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z))) :
    forall x y z : BHist, hsame (mul x (add y z)) (add (mul y x) (mul z x)) := by
  intro x y z
  exact hsame_trans (leftDistrib x y z)
    (addCongr (mulComm x y) (mulComm x z))

theorem commring_difference_of_squares {add mul : BHist -> BHist -> BHist}
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
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x)) :
    forall a b : BHist,
      hsame (mul (add a b) (add a (neg b))) (add (mul a a) (neg (mul b b))) := by
  have rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
    exact commring_right_distrib_from_left mulComm addCongr leftDistrib
  have mulNegRight : forall x y : BHist, hsame (mul x (neg y)) (neg (mul x y)) := by
    exact BEDC.Derived.RingUp.ring_mul_neg_right_eq_neg_mul addAssoc addComm zeroLeft
      negLeft addCongr mulCongr leftDistrib rightDistrib
  intro a b
  have expanded :
      hsame (mul (add a b) (add a (neg b)))
        (add (add (mul a a) (mul a (neg b))) (add (mul b a) (mul b (neg b)))) := by
    exact commring_mul_add_add_expand mulComm addCongr leftDistrib a b a (neg b)
  have normalizedProducts :
      hsame (add (add (mul a a) (mul a (neg b))) (add (mul b a) (mul b (neg b))))
        (add (add (mul a a) (neg (mul a b))) (add (mul a b) (neg (mul b b)))) := by
    exact addCongr
      (addCongr (hsame_refl (mul a a)) (mulNegRight a b))
      (addCongr (mulComm b a) (mulNegRight b b))
  have collapseMiddle :
      hsame (add (add (mul a a) (neg (mul a b))) (add (mul a b) (neg (mul b b))))
        (add (mul a a) (neg (mul b b))) := by
    have reassocLeft :
        hsame (add (add (mul a a) (neg (mul a b))) (add (mul a b) (neg (mul b b))))
          (add (mul a a) (add (neg (mul a b)) (add (mul a b) (neg (mul b b))))) := by
      exact addAssoc (mul a a) (neg (mul a b)) (add (mul a b) (neg (mul b b)))
    have reassocMiddle :
        hsame (add (neg (mul a b)) (add (mul a b) (neg (mul b b))))
          (add (add (neg (mul a b)) (mul a b)) (neg (mul b b))) := by
      exact hsame_symm (addAssoc (neg (mul a b)) (mul a b) (neg (mul b b)))
    have cancelMiddle :
        hsame (add (add (neg (mul a b)) (mul a b)) (neg (mul b b)))
          (add zero (neg (mul b b))) := by
      exact addCongr (negLeft (mul a b)) (hsame_refl (neg (mul b b)))
    exact hsame_trans reassocLeft
      (addCongr (hsame_refl (mul a a))
        (hsame_trans reassocMiddle (hsame_trans cancelMiddle (zeroLeft (neg (mul b b))))))
  exact hsame_trans expanded (hsame_trans normalizedProducts collapseMiddle)

end BEDC.Derived.CommRingUp
