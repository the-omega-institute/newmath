import BEDC.Derived.FieldUp.ProductInverseClassifier
import BEDC.FKernel.Cont

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RatupFieldupInverseProductClassifierExitRow {mul : BHist → BHist → BHist}
    {one : BHist} {NonZero : BHist → Prop} {inv : (a : BHist) → NonZero a → BHist}
    (assocC : ∀ x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x : BHist, hsame (mul one x) x)
    (rightId : ∀ x : BHist, hsame (mul x one) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (leftInv : ∀ (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : ∀ (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (apartToNonzero : ∀ {h : BHist}, (hsame h BHist.Empty → False) → NonZero h)
    {a b c d : BHist} (pabApart : hsame (mul a b) BHist.Empty → False)
    (pcdApart : hsame (mul c d) BHist.Empty → False)
    (pa : NonZero a) (pb : NonZero b) (pc : NonZero c) (pd : NonZero d) :
    hsame (mul a b) (mul c d) ↔
      hsame (append (mul (inv b pb) (inv a pa)) BHist.Empty)
        (append (mul (inv d pd) (inv c pc)) BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist hsame append
  have exactness :
      hsame (mul a b) (mul c d) ↔
        hsame (mul (inv b pb) (inv a pa)) (mul (inv d pd) (inv c pc)) := by
    exact field_apart_product_inverse_classifier_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv apartToNonzero pabApart pcdApart
      pa pb pc pd
  constructor
  · intro sameProduct
    have sameReverse :
        hsame (mul (inv b pb) (inv a pa)) (mul (inv d pd) (inv c pc)) :=
      Iff.mp exactness sameProduct
    exact hsame_trans (hsame_symm (append_empty_right (mul (inv b pb) (inv a pa))))
      (hsame_trans sameReverse (append_empty_right (mul (inv d pd) (inv c pc))))
  · intro sameExit
    have sameReverse :
        hsame (mul (inv b pb) (inv a pa)) (mul (inv d pd) (inv c pc)) :=
      hsame_trans (append_empty_right (mul (inv b pb) (inv a pa)))
        (hsame_trans sameExit (hsame_symm (append_empty_right (mul (inv d pd) (inv c pc)))))
    exact Iff.mpr exactness sameReverse

end BEDC.Derived.FieldUp
