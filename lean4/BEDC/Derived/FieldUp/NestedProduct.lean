import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_nested_product_nonzero_excludes_empty_factors
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    {NonZero : BHist -> Prop}
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
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroEmptyAbsurd : NonZero BHist.Empty -> False)
    {a x b : BHist} :
    NonZero (mul (mul a x) b) ->
      (hsame a BHist.Empty -> False) ∧
        (hsame x BHist.Empty -> False) ∧ (hsame b BHist.Empty -> False) := by
  intro productNonzero
  have zeroAbsorption :=
    BEDC.Derived.RingUp.ring_mul_zero_absorption addAssoc zeroLeft negLeft
      addCongr mulCongr leftDistrib rightDistrib
  constructor
  · intro aEmpty
    have innerEmpty : hsame (mul a x) BHist.Empty := by
      exact hsame_trans (mulCongr aEmpty (hsame_refl x)) (zeroAbsorption.right x)
    have productEmpty : hsame (mul (mul a x) b) BHist.Empty := by
      exact hsame_trans (mulCongr innerEmpty (hsame_refl b)) (zeroAbsorption.right b)
    exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)
  · constructor
    · intro xEmpty
      have innerEmpty : hsame (mul a x) BHist.Empty := by
        exact hsame_trans (mulCongr (hsame_refl a) xEmpty) (zeroAbsorption.left a)
      have productEmpty : hsame (mul (mul a x) b) BHist.Empty := by
        exact hsame_trans (mulCongr innerEmpty (hsame_refl b)) (zeroAbsorption.right b)
      exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)
    · intro bEmpty
      have productEmpty : hsame (mul (mul a x) b) BHist.Empty := by
        exact hsame_trans (mulCongr (hsame_refl (mul a x)) bEmpty)
          (zeroAbsorption.left (mul a x))
      exact nonzeroEmptyAbsurd (nonzeroTransport productEmpty productNonzero)

end BEDC.Derived.FieldUp
