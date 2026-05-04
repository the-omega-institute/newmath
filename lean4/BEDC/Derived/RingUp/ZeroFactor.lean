import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp
open BEDC.FKernel.Hist

theorem ring_zero_classifier_factor_absorption {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x y : BHist} :
    hsame x BHist.Empty -> hsame (mul x y) BHist.Empty ∧
      hsame (mul y x) BHist.Empty := by
  intro xEmpty
  have zeroAbsorption :=
    ring_mul_zero_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib
  constructor
  · exact hsame_trans (mulCongr xEmpty (hsame_refl y)) (zeroAbsorption.right y)
  · exact hsame_trans (mulCongr (hsame_refl y) xEmpty) (zeroAbsorption.left y)

theorem ring_zero_classifier_signed_factor_absorption
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    {x y : BHist} :
    hsame x BHist.Empty -> hsame (mul (neg x) y) BHist.Empty ∧
      hsame (mul y (neg x)) BHist.Empty ∧
      hsame (mul (neg x) (neg y)) BHist.Empty ∧
      hsame (mul (neg y) (neg x)) BHist.Empty := by
  intro xEmpty
  have negEmpty :
      hsame (neg x) BHist.Empty :=
    hsame_trans (negCongr xEmpty)
      (ring_neg_zero (add := add) (neg := neg) (zero := BHist.Empty) addComm zeroLeft negLeft)
  have plainAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := neg x) (y := y) negEmpty
  have signedAbsorption :=
    ring_zero_classifier_factor_absorption addAssoc zeroLeft negLeft addCongr mulCongr
      leftDistrib rightDistrib (x := neg x) (y := neg y) negEmpty
  exact ⟨plainAbsorption.left, plainAbsorption.right,
    signedAbsorption.left, signedAbsorption.right⟩

end BEDC.Derived.RingUp
