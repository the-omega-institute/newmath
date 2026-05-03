import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

def GroupConjugationWord (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist)
    (s x : BHist) : BHist :=
  mul (mul s x) (inv s)

protected theorem group_conjugation_composition_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {s t x : BHist} :
    hsame (mul (mul (mul s t) x) (inv (mul s t)))
      (mul (mul s (mul (mul t x) (inv t))) (inv s)) := by
  have reverseInv : hsame (inv (mul s t)) (mul (inv t) (inv s)) :=
    group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv s t
  have alignInverse :
      hsame (mul (mul (mul s t) x) (inv (mul s t)))
        (mul (mul (mul s t) x) (mul (inv t) (inv s))) :=
    mulCongr (hsame_refl (mul (mul s t) x)) reverseInv
  have alignHead :
      hsame (mul (mul (mul s t) x) (mul (inv t) (inv s)))
        (mul (mul s (mul t x)) (mul (inv t) (inv s))) :=
    mulCongr (assocC s t x) (hsame_refl (mul (inv t) (inv s)))
  have reassocOuter :
      hsame (mul (mul s (mul t x)) (mul (inv t) (inv s)))
        (mul s (mul (mul t x) (mul (inv t) (inv s)))) :=
    assocC s (mul t x) (mul (inv t) (inv s))
  have reassocInner :
      hsame (mul s (mul (mul t x) (mul (inv t) (inv s))))
        (mul s (mul (mul (mul t x) (inv t)) (inv s))) :=
    mulCongr (hsame_refl s) (hsame_symm (assocC (mul t x) (inv t) (inv s)))
  have exposeTail :
      hsame (mul s (mul (mul (mul t x) (inv t)) (inv s)))
        (mul (mul s (mul (mul t x) (inv t))) (inv s)) :=
    hsame_symm (assocC s (mul (mul t x) (inv t)) (inv s))
  exact hsame_trans alignInverse
    (hsame_trans alignHead
      (hsame_trans reassocOuter (hsame_trans reassocInner exposeTail)))

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
  exact BEDC.Derived.GroupUp.group_conjugation_composition_from_empty_unit
    assocC leftId rightId mulCongr leftInv rightInv

end BEDC.Derived.GroupUp
