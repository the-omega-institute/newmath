import BEDC.Derived.CommRingUp
import BEDC.Derived.RingUp.ZeroFactor

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist

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
