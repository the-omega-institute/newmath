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

end BEDC.Derived.FieldUp
