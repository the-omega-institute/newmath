import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

def FieldApartZero (a : BHist) : Prop :=
  hsame a BHist.Empty -> False

theorem field_product_apartness_inverse_product_reverse
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {inv : (a : BHist) -> FieldApartZero a -> BHist}
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
    (leftInv : forall (a : BHist) (p : FieldApartZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : FieldApartZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pa : FieldApartZero a) (pb : FieldApartZero b) :
    Exists (fun pab : FieldApartZero (mul a b) =>
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa))) := by
  have productApart : FieldApartZero (mul a b) := by
    intro productEmpty
    have zeroCancel :=
      field_one_sided_zero_product_cancel_from_apartness
        (NonZero := FieldApartZero) (inv := inv) addAssoc zeroLeft negLeft
        assocC leftId rightId addCongr mulCongr leftDistrib rightDistrib leftInv rightInv a b
    exact pb (zeroCancel.left pa productEmpty)
  exact Exists.intro productApart
    (field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv productApart pa pb)

end BEDC.Derived.FieldUp
