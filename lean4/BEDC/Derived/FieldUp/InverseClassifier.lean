import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_inverse_empty_unit_classifier_exact_from_apartness_iff
    {mul : BHist -> BHist -> BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a),
      hsame (mul (inv a p) a) BHist.Empty)
    (rightInv : forall (a : BHist) (p : NonZero a),
      hsame (mul a (inv a p)) BHist.Empty)
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame a b <-> hsame (inv a pa) (inv b pb) := by
  constructor
  · intro sameAB
    exact field_inverse_congruence_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv sameAB pa pb
  · intro sameInv
    exact field_inverse_cancel_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pb sameInv

end BEDC.Derived.FieldUp
