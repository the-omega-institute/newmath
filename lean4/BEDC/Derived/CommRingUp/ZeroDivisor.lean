import BEDC.Derived.CommRingUp
import BEDC.Derived.RingUp.ZeroFactor

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

def CommRingApartZero (x : BHist) : Prop :=
  hsame x BHist.Empty -> False

theorem CommRingApartZero_visible_pair {h : BHist} :
    CommRingApartZero (BHist.e0 h) ∧ CommRingApartZero (BHist.e1 h) := by
  constructor
  · intro same
    exact not_hsame_e0_empty same
  · intro same
    exact not_hsame_e1_empty same

def CommRingLeftZeroDivisor (mul : BHist -> BHist -> BHist) (x : BHist) : Prop :=
  CommRingApartZero x ∧
    Exists (fun c : BHist => CommRingApartZero c ∧ hsame (mul x c) BHist.Empty)

theorem CommRingLeftZeroDivisor_strict_of_mul_comm {mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x)) {x : BHist} :
    CommRingLeftZeroDivisor mul x ->
      CommRingApartZero x ∧
        Exists (fun c : BHist =>
          CommRingApartZero c ∧ hsame (mul x c) BHist.Empty ∧
            hsame (mul c x) BHist.Empty) := by
  intro leftZD
  cases leftZD.right with
  | intro c witness =>
      exact And.intro leftZD.left
        (Exists.intro c
            (And.intro witness.left
              (And.intro witness.right (hsame_trans (mulComm c x) witness.right))))

theorem CommRingLeftZeroDivisor_strict_expansion_iff_of_mul_comm
    {mul : BHist -> BHist -> BHist}
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x)) {x : BHist} :
    CommRingLeftZeroDivisor mul x <->
      ((hsame x BHist.Empty -> False) ∧
        Exists (fun c : BHist =>
          (hsame c BHist.Empty -> False) ∧ hsame (mul x c) BHist.Empty ∧
            hsame (mul c x) BHist.Empty)) := by
  constructor
  · intro leftZD
    exact CommRingLeftZeroDivisor_strict_of_mul_comm mulComm leftZD
  · intro strictZD
    cases strictZD.right with
    | intro c witness =>
        exact And.intro strictZD.left
          (Exists.intro c (And.intro witness.left witness.right.left))

theorem CommRingLeftZeroDivisor_product_closed {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    {a b : BHist} :
    CommRingLeftZeroDivisor mul a ->
      CommRingApartZero (mul a b) ->
        CommRingLeftZeroDivisor mul (mul a b) := by
  intro leftZD productApart
  cases leftZD.right with
  | intro c data =>
      have rightDistrib : forall x y z : BHist,
          hsame (mul (add x y) z) (add (mul x z) (mul y z)) := by
        exact commring_right_distrib_from_left mulComm addCongr leftDistrib
      have zeroAbsorption :
          And (forall x : BHist, hsame (mul x BHist.Empty) BHist.Empty)
            (forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty) :=
        BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
          addCongr mulCongr leftDistrib rightDistrib
      have sameReassoc :
          hsame (mul (mul a b) c) (mul a (mul c b)) := by
        exact hsame_trans (mulAssoc a b c)
          (mulCongr (hsame_refl a) (mulComm b c))
      have sameToLeftProduct :
          hsame (mul a (mul c b)) (mul (mul a c) b) := by
        exact hsame_symm (mulAssoc a c b)
      have leftProductZero : hsame (mul (mul a c) b) BHist.Empty := by
        exact hsame_trans
          (mulCongr data.right (hsame_refl b))
          (zeroAbsorption.right b)
      constructor
      · exact productApart
      · exact Exists.intro c
          (And.intro data.left
            (hsame_trans sameReassoc
              (hsame_trans sameToLeftProduct leftProductZero)))

theorem commring_strict_zero_divisor_empty_product_closed
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulComm : forall x y : BHist, hsame (mul x y) (mul y x))
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z))) {a b : BHist} :
    let ApartZero := fun x : BHist => hsame x BHist.Empty -> False
    let StrictZD := fun x : BHist =>
      ApartZero x ∧ Exists (fun c : BHist =>
        ApartZero c ∧ hsame (mul x c) BHist.Empty ∧ hsame (mul c x) BHist.Empty)
    StrictZD a -> ApartZero (mul a b) -> StrictZD (mul a b) := by
  dsimp
  intro strictA productApart
  cases strictA.right with
  | intro c witness =>
      have leftAbsorption :=
        BEDC.Derived.RingUp.ring_zero_classifier_factor_absorption
          addAssoc zeroLeft negLeft addCongr mulCongr leftDistrib rightDistrib
          (x := mul a c) (y := b) witness.right.left
      have leftProductZero : hsame (mul (mul a b) c) BHist.Empty :=
        hsame_trans (mulAssoc a b c)
          (hsame_trans
            (mulCongr (hsame_refl a) (mulComm b c))
            (hsame_trans (hsame_symm (mulAssoc a c b)) leftAbsorption.left))
      have rightProductZero : hsame (mul c (mul a b)) BHist.Empty :=
        hsame_trans (hsame_symm (mulComm (mul a b) c)) leftProductZero
      exact And.intro productApart
        (Exists.intro c (And.intro witness.left
          (And.intro leftProductZero rightProductZero)))

end BEDC.Derived.CommRingUp
