import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_conjugation_equation_exact_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeftMul : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    {a x b : BHist} (pa : NonZero a) :
    hsame (mul (mul a x) (inv a pa)) b <->
      hsame x (mul (inv a pa) (mul b a)) := by
  have pinv : NonZero (inv a pa) :=
    field_inverse_nonzero_from_one_apartness mulCongr zeroLeftMul leftInv oneApartEmpty
      nonzeroOfApartEmpty pa
  have doubleInverse : hsame (inv (inv a pa) pinv) a := by
    exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC
      leftId
      rightId
      mulCongr
      (leftInv (inv a pa) pinv)
      (leftInv a pa)
  have middleExact :
      hsame (mul (mul a x) (inv a pa)) b <->
        hsame x (mul (inv a pa) (mul b (inv (inv a pa) pinv))) :=
    field_middle_mul_equation_exact_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pa pinv
  constructor
  · intro sameConjugation
    have solved := Iff.mp middleExact sameConjugation
    exact hsame_trans solved
      (mulCongr (hsame_refl (inv a pa)) (mulCongr (hsame_refl b) doubleInverse))
  · intro solved
    apply Iff.mpr middleExact
    exact hsame_trans solved
      (hsame_symm
        (mulCongr (hsame_refl (inv a pa)) (mulCongr (hsame_refl b) doubleInverse)))

theorem field_apart_empty_conjugation_equation_exact {mul : BHist -> BHist -> BHist}
    {one : BHist} {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul a (inv a p)) one)
    {a x b : BHist} (pa : hsame a BHist.Empty -> False) :
    hsame (mul (mul a x) (inv a pa)) b <->
      hsame x (mul (mul (inv a pa) b) a) := by
  constructor
  · intro sameConjugate
    have collapseRight :
        hsame (mul (mul (mul a x) (inv a pa)) a) (mul a x) := by
      exact hsame_trans (assocC (mul a x) (inv a pa) a)
        (hsame_trans (mulCongr (hsame_refl (mul a x)) (leftInv a pa))
          (rightId (mul a x)))
    have sameLeftProduct : hsame (mul a x) (mul b a) := by
      exact hsame_trans (hsame_symm collapseRight)
        (mulCongr sameConjugate (hsame_refl a))
    have solveLeft : hsame x (mul (inv a pa) (mul b a)) := by
      exact Iff.mp
        (field_left_mul_equation_exact_from_apartness
          assocC leftId mulCongr leftInv rightInv pa)
        sameLeftProduct
    exact hsame_trans solveLeft (hsame_symm (assocC (inv a pa) b a))
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
          hsame (mul (mul (mul a (inv a pa)) b) a) (mul (mul one b) a) := by
        exact mulCongr (mulCongr (rightInv a pa) (hsame_refl b)) (hsame_refl a)
      have collapseUnit : hsame (mul (mul one b) a) (mul b a) := by
        exact mulCongr (leftId b) (hsame_refl a)
      exact hsame_trans replaceMiddle
        (hsame_trans reassocOuter
          (hsame_trans reassocInner (hsame_trans collapseHead collapseUnit)))
    exact hsame_trans (mulCongr sameLeftProduct (hsame_refl (inv a pa)))
      (hsame_trans (assocC b a (inv a pa))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a pa)) (rightId b)))

theorem field_apart_empty_inverse_conjugation_equation_exact
    {mul : BHist -> BHist -> BHist}
    {one : BHist} {inv : (a : BHist) -> (hsame a BHist.Empty -> False) -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : hsame a BHist.Empty -> False),
      hsame (mul a (inv a p)) one)
    {a x b : BHist} (pa : hsame a BHist.Empty -> False) :
    hsame (mul (mul (inv a pa) x) a) b <->
      hsame x (mul (mul a b) (inv a pa)) := by
  constructor
  · intro sameConjugate
    have collapseRight :
        hsame (mul (mul (mul (inv a pa) x) a) (inv a pa))
          (mul (inv a pa) x) := by
      exact hsame_trans (assocC (mul (inv a pa) x) a (inv a pa))
        (hsame_trans (mulCongr (hsame_refl (mul (inv a pa) x)) (rightInv a pa))
          (rightId (mul (inv a pa) x)))
    have sameRightProduct : hsame (mul (inv a pa) x) (mul b (inv a pa)) := by
      exact hsame_trans (hsame_symm collapseRight)
        (mulCongr sameConjugate (hsame_refl (inv a pa)))
    have transported :
        hsame (mul a (mul (inv a pa) x)) (mul a (mul b (inv a pa))) := by
      exact mulCongr (hsame_refl a) sameRightProduct
    have collapseLeft : hsame (mul a (mul (inv a pa) x)) x := by
      exact hsame_trans (hsame_symm (assocC a (inv a pa) x))
        (hsame_trans (mulCongr (rightInv a pa) (hsame_refl x)) (leftId x))
    exact hsame_trans (hsame_symm collapseLeft)
      (hsame_trans transported (hsame_symm (assocC a b (inv a pa))))
  · intro sameMiddle
    have sameRightProduct : hsame (mul (inv a pa) x) (mul b (inv a pa)) := by
      have replaceMiddle :
          hsame (mul (inv a pa) x)
            (mul (inv a pa) (mul (mul a b) (inv a pa))) := by
        exact mulCongr (hsame_refl (inv a pa)) sameMiddle
      have reassocOuter :
          hsame (mul (inv a pa) (mul (mul a b) (inv a pa)))
            (mul (mul (inv a pa) (mul a b)) (inv a pa)) := by
        exact hsame_symm (assocC (inv a pa) (mul a b) (inv a pa))
      have reassocInner :
          hsame (mul (mul (inv a pa) (mul a b)) (inv a pa))
            (mul (mul (mul (inv a pa) a) b) (inv a pa)) := by
        exact mulCongr (hsame_symm (assocC (inv a pa) a b)) (hsame_refl (inv a pa))
      have collapseHead :
          hsame (mul (mul (mul (inv a pa) a) b) (inv a pa))
            (mul (mul one b) (inv a pa)) := by
        exact mulCongr (mulCongr (leftInv a pa) (hsame_refl b))
          (hsame_refl (inv a pa))
      have collapseUnit :
          hsame (mul (mul one b) (inv a pa)) (mul b (inv a pa)) := by
        exact mulCongr (leftId b) (hsame_refl (inv a pa))
      exact hsame_trans replaceMiddle
        (hsame_trans reassocOuter
          (hsame_trans reassocInner (hsame_trans collapseHead collapseUnit)))
    exact hsame_trans (mulCongr sameRightProduct (hsame_refl a))
      (hsame_trans (assocC b (inv a pa) a)
        (hsame_trans (mulCongr (hsame_refl b) (leftInv a pa)) (rightId b)))

end BEDC.Derived.FieldUp
