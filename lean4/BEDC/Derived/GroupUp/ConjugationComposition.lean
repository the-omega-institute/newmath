import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

def GroupConjugationWord (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist)
    (s x : BHist) : BHist :=
  mul (mul s x) (inv s)

theorem GroupConjugationWord_product_composition
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {s t x : BHist} :
    hsame (GroupConjugationWord mul inv (mul s t) x)
      (GroupConjugationWord mul inv s (GroupConjugationWord mul inv t x)) := by
  have inverseProduct :
      hsame (inv (mul s t)) (mul (inv t) (inv s)) := by
    exact group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv s t
  have replaceInverse :
      hsame (mul (mul (mul s t) x) (inv (mul s t)))
        (mul (mul (mul s t) x) (mul (inv t) (inv s))) := by
    exact mulCongr (hsame_refl (mul (mul s t) x)) inverseProduct
  have exposeRightInverse :
      hsame (mul (mul (mul s t) x) (mul (inv t) (inv s)))
        (mul (mul (mul (mul s t) x) (inv t)) (inv s)) := by
    exact hsame_symm (assocC (mul (mul s t) x) (inv t) (inv s))
  have reassociateProduct :
      hsame (mul (mul (mul (mul s t) x) (inv t)) (inv s))
        (mul (mul (mul s t) (mul x (inv t))) (inv s)) := by
    exact mulCongr (assocC (mul s t) x (inv t)) (hsame_refl (inv s))
  have exposeOuter :
      hsame (mul (mul (mul s t) (mul x (inv t))) (inv s))
        (mul (mul s (mul t (mul x (inv t)))) (inv s)) := by
    exact mulCongr (assocC s t (mul x (inv t))) (hsame_refl (inv s))
  have exposeInner :
      hsame (mul (mul s (mul t (mul x (inv t)))) (inv s))
        (mul (mul s (mul (mul t x) (inv t))) (inv s)) := by
    exact mulCongr (mulCongr (hsame_refl s) (hsame_symm (assocC t x (inv t))))
      (hsame_refl (inv s))
  exact hsame_trans replaceInverse
    (hsame_trans exposeRightInverse
      (hsame_trans reassociateProduct (hsame_trans exposeOuter exposeInner)))

end BEDC.Derived.GroupUp
