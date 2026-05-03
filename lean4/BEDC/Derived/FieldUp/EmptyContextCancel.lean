import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

protected theorem field_nonzero_mul_empty_context_cancel_from_apartness
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y u v : BHist} (pa : NonZero a) (pb : NonZero b) :
    (hsame (mul x b) (append BHist.Empty (mul y b)) -> hsame x y) ∧
      (hsame (mul a u) (append BHist.Empty (mul a v)) -> hsame u v) := by
  constructor
  · intro sameProduct
    have solvedX : hsame x (mul (append BHist.Empty (mul y b)) (inv b pb)) := by
      exact field_right_mul_equation_solution_from_apartness
        assocC rightId mulCongr rightInv pb sameProduct
    have emptyContext :
        hsame (append BHist.Empty (mul y b)) (mul y b) :=
      append_empty_left (mul y b)
    have transportEndpoint :
        hsame (mul (append BHist.Empty (mul y b)) (inv b pb))
          (mul (mul y b) (inv b pb)) := by
      exact mulCongr emptyContext (hsame_refl (inv b pb))
    have cancelY : hsame (mul (mul y b) (inv b pb)) y := by
      exact field_mul_inverse_right_cancel_from_apartness
        assocC rightId mulCongr rightInv y b pb
    exact hsame_trans solvedX (hsame_trans transportEndpoint cancelY)
  · intro sameProduct
    have solvedU : hsame u (mul (inv a pa) (append BHist.Empty (mul a v))) := by
      exact Iff.mp
        (field_left_mul_equation_exact_from_apartness
          assocC leftId mulCongr leftInv rightInv pa)
        sameProduct
    have emptyContext :
        hsame (append BHist.Empty (mul a v)) (mul a v) :=
      append_empty_left (mul a v)
    have transportEndpoint :
        hsame (mul (inv a pa) (append BHist.Empty (mul a v)))
          (mul (inv a pa) (mul a v)) := by
      exact mulCongr (hsame_refl (inv a pa)) emptyContext
    have cancelV : hsame (mul (inv a pa) (mul a v)) v := by
      exact field_mul_inverse_left_cancel_from_apartness
        assocC leftId mulCongr leftInv a v pa
    exact hsame_trans solvedU (hsame_trans transportEndpoint cancelV)

end BEDC.Derived.FieldUp
