import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_empty_unit_conjugation_equation_exact_from_apartness
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
    {a x b : BHist} (pa : NonZero a) :
    hsame (mul (mul a x) (inv a pa)) b <->
      hsame x (mul (mul (inv a pa) b) a) := by
  constructor
  · intro sameConj
    have collapseConjRight :
        hsame (mul (mul (mul a x) (inv a pa)) a) (mul a x) := by
      exact hsame_trans (assocC (mul a x) (inv a pa) a)
        (hsame_trans (mulCongr (hsame_refl (mul a x)) (leftInv a pa))
          (rightId (mul a x)))
    have sameLeftProduct : hsame (mul a x) (mul b a) := by
      exact hsame_trans (hsame_symm collapseConjRight)
        (mulCongr sameConj (hsame_refl a))
    exact hsame_trans (hsame_symm (leftId x))
      (hsame_trans (mulCongr (hsame_symm (leftInv a pa)) (hsame_refl x))
        (hsame_trans (assocC (inv a pa) a x)
          (hsame_trans (mulCongr (hsame_refl (inv a pa)) sameLeftProduct)
            (hsame_symm (assocC (inv a pa) b a)))))
  · intro sameMiddle
    have sameLeftProduct : hsame (mul a x) (mul b a) := by
      have replaceMiddle :
          hsame (mul a x) (mul a (mul (mul (inv a pa) b) a)) := by
        exact mulCongr (hsame_refl a) sameMiddle
      have reassocOuter :
          hsame (mul a (mul (mul (inv a pa) b) a))
            (mul (mul a (mul (inv a pa) b)) a) := by
        exact hsame_symm (assocC a (mul (inv a pa) b) a)
      have reassocInner :
          hsame (mul (mul a (mul (inv a pa) b)) a)
            (mul (mul (mul a (inv a pa)) b) a) := by
        exact mulCongr (hsame_symm (assocC a (inv a pa) b)) (hsame_refl a)
      have collapseHead :
          hsame (mul (mul (mul a (inv a pa)) b) a) (mul (mul BHist.Empty b) a) := by
        exact mulCongr (mulCongr (rightInv a pa) (hsame_refl b)) (hsame_refl a)
      have collapseUnit : hsame (mul (mul BHist.Empty b) a) (mul b a) := by
        exact mulCongr (leftId b) (hsame_refl a)
      exact hsame_trans replaceMiddle
        (hsame_trans reassocOuter
          (hsame_trans reassocInner (hsame_trans collapseHead collapseUnit)))
    exact hsame_trans (mulCongr sameLeftProduct (hsame_refl (inv a pa)))
      (hsame_trans (assocC b a (inv a pa))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a pa)) (rightId b)))

protected theorem field_empty_unit_conjugation_classifier_exact_from_apartness
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
    {a x y : BHist} (pa : NonZero a) :
    hsame (mul (mul a x) (inv a pa)) (mul (mul a y) (inv a pa)) <->
      hsame x y := by
  constructor
  · intro sameConj
    have sameXTarget :
        hsame x (mul (mul (inv a pa) (mul (mul a y) (inv a pa))) a) := by
      exact (BEDC.Derived.FieldUp.field_empty_unit_conjugation_equation_exact_from_apartness
        assocC leftId rightId mulCongr leftInv rightInv pa).mp sameConj
    have sameYTarget :
        hsame y (mul (mul (inv a pa) (mul (mul a y) (inv a pa))) a) := by
      exact (BEDC.Derived.FieldUp.field_empty_unit_conjugation_equation_exact_from_apartness
        assocC leftId rightId mulCongr leftInv rightInv pa).mp
          (hsame_refl (mul (mul a y) (inv a pa)))
    exact hsame_trans sameXTarget (hsame_symm sameYTarget)
  · intro sameXY
    exact mulCongr (mulCongr (hsame_refl a) sameXY) (hsame_refl (inv a pa))

end BEDC.Derived.FieldUp
