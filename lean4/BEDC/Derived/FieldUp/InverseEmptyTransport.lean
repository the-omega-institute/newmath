import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_inverse_apart_empty_hsame_transport {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (sameAB : hsame a b) (pa : NonZero a) (pb : NonZero b) :
    (hsame (inv a pa) BHist.Empty -> False) ->
      hsame (inv b pb) BHist.Empty -> False := by
  intro apartA inverseBEmpty
  have sameInv : hsame (inv a pa) (inv b pb) :=
    field_inverse_congruence_from_apartness assocC leftId rightId mulCongr leftInv rightInv
      sameAB pa pb
  exact apartA (hsame_trans sameInv inverseBEmpty)

protected theorem field_inverse_empty_endpoint_reflection_from_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (inv a pa) (inv b pb) ->
      (hsame a BHist.Empty <-> hsame b BHist.Empty) := by
  intro sameInv
  have sameAB : hsame a b :=
    field_inverse_cancel_from_apartness assocC leftId rightId mulCongr leftInv rightInv
      pa pb sameInv
  constructor
  · intro aEmpty
    exact hsame_trans (hsame_symm sameAB) aEmpty
  · intro bEmpty
    exact hsame_trans sameAB bEmpty

end BEDC.Derived.FieldUp
