import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_two_sided_mul_empty_solution_unique_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftDistrib : forall x y z : BHist,
      hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib : forall x y z : BHist,
      hsame (mul (add x y) z) (add (mul x z) (mul y z)))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (mul a x) b) BHist.Empty ->
      hsame (mul (mul a y) b) BHist.Empty -> hsame x y := by
  intro productX productY
  have xEmpty : hsame x BHist.Empty := by
    exact Iff.mp
      (field_two_sided_empty_product_exact_from_apartness addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
        pa pb)
      productX
  have yEmpty : hsame y BHist.Empty := by
    exact Iff.mp
      (field_two_sided_empty_product_exact_from_apartness addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv
        pa pb)
      productY
  exact hsame_trans xEmpty (hsame_symm yEmpty)

end BEDC.Derived.FieldUp
