import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem RatupFieldupAffineInnerConjugationExit {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (_rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {T V W : BHist} (pT : NonZero T) :
    hsame (mul (mul T V) (inv T pT)) W ->
      hsame V (mul (inv T pT) (mul W T)) := by
  intro sameConjugate
  have collapseRight :
      hsame (mul (mul (mul T V) (inv T pT)) T) (mul T V) := by
    exact hsame_trans (assocC (mul T V) (inv T pT) T)
      (hsame_trans (mulCongr (hsame_refl (mul T V)) (leftInv T pT))
        (rightId (mul T V)))
  have sameLeftProduct : hsame (mul T V) (mul W T) := by
    exact hsame_trans (hsame_symm collapseRight)
      (mulCongr sameConjugate (hsame_refl T))
  have expandByUnit : hsame V (mul one V) :=
    hsame_symm (leftId V)
  have replaceUnit : hsame (mul one V) (mul (mul (inv T pT) T) V) :=
    mulCongr (hsame_symm (leftInv T pT)) (hsame_refl V)
  have reassociate :
      hsame (mul (mul (inv T pT) T) V) (mul (inv T pT) (mul T V)) :=
    assocC (inv T pT) T V
  have transportMiddle :
      hsame (mul (inv T pT) (mul T V)) (mul (inv T pT) (mul W T)) :=
    mulCongr (hsame_refl (inv T pT)) sameLeftProduct
  exact hsame_trans expandByUnit
    (hsame_trans replaceUnit (hsame_trans reassociate transportMiddle))

end BEDC.Derived.FieldUp
