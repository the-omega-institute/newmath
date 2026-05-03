import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

theorem group_centralizer_empty_unit_mem {mul : BHist -> BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    {a : BHist} :
    hsame (mul BHist.Empty a) (mul a BHist.Empty) := by
  exact hsame_trans (leftId a) (hsame_symm (rightId a))

protected theorem group_centralizer_inv_closed_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    hsame (mul x a) (mul a x) -> hsame (mul (inv x) a) (mul a (inv x)) := by
  intro commute
  have transportedLeft :
      hsame (mul (inv x) (mul x a)) (mul (inv x) (mul a x)) := by
    exact mulCongr (hsame_refl (inv x)) commute
  have collapseLeft : hsame (mul (inv x) (mul x a)) a := by
    exact hsame_trans (hsame_symm (assocC (inv x) x a))
      (hsame_trans (mulCongr (leftInv x) (hsame_refl a)) (leftId a))
  have bridge : hsame a (mul (inv x) (mul a x)) := by
    exact hsame_trans (hsame_symm collapseLeft) transportedLeft
  have transportedRight :
      hsame (mul a (inv x)) (mul (mul (inv x) (mul a x)) (inv x)) := by
    exact mulCongr bridge (hsame_refl (inv x))
  have reassocRight :
      hsame (mul (mul (inv x) (mul a x)) (inv x))
        (mul (inv x) (mul (mul a x) (inv x))) := by
    exact assocC (inv x) (mul a x) (inv x)
  have collapseRight : hsame (mul (mul a x) (inv x)) a := by
    exact hsame_trans (assocC a x (inv x))
      (hsame_trans (mulCongr (hsame_refl a) (rightInv x)) (rightId a))
  have final :
      hsame (mul a (inv x)) (mul (inv x) a) := by
    exact hsame_trans transportedRight
      (hsame_trans reassocRight (mulCongr (hsame_refl (inv x)) collapseRight))
  exact hsame_symm final

theorem group_centralizer_mul_closed_empty_context {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y : BHist} :
    hsame (mul x a) (mul a x) -> hsame (mul y a) (mul a y) ->
      hsame (mul (mul (mul x y) a) BHist.Empty)
        (mul (mul a (mul x y)) BHist.Empty) := by
  intro commuteX commuteY
  have leftAssoc : hsame (mul (mul x y) a) (mul x (mul y a)) := by
    exact assocC x y a
  have transportY : hsame (mul x (mul y a)) (mul x (mul a y)) := by
    exact mulCongr (hsame_refl x) commuteY
  have reassocXY : hsame (mul x (mul a y)) (mul (mul x a) y) := by
    exact hsame_symm (assocC x a y)
  have transportX : hsame (mul (mul x a) y) (mul (mul a x) y) := by
    exact mulCongr commuteX (hsame_refl y)
  have rightAssoc : hsame (mul (mul a x) y) (mul a (mul x y)) := by
    exact assocC a x y
  have productClosed : hsame (mul (mul x y) a) (mul a (mul x y)) := by
    exact hsame_trans leftAssoc
      (hsame_trans transportY
        (hsame_trans reassocXY (hsame_trans transportX rightAssoc)))
  exact mulCongr productClosed (hsame_refl BHist.Empty)

protected theorem group_centralizer_mul_closed_from_empty_unit {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y : BHist} :
    hsame (mul x a) (mul a x) -> hsame (mul y a) (mul a y) ->
      hsame (mul (mul x y) a) (mul a (mul x y)) := by
  intro commuteX commuteY
  have wrapped :=
    group_centralizer_mul_closed_empty_context (mul := mul) assocC mulCongr commuteX commuteY
  exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
    (hsame_trans wrapped (rightId (mul a (mul x y))))

end BEDC.Derived.GroupUp
