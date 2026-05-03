import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_inverse_nonzero_domain_automorphism {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeft : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    {a b : BHist} (pa : NonZero a) (pb : NonZero b) :
    ∃ pA : NonZero (inv a pa),
      hsame (inv (inv a pa) pA) a ∧
        (hsame (inv a pa) (inv b pb) ↔ hsame a b) := by
  let pA : NonZero (inv a pa) :=
    field_inverse_nonzero_from_one_apartness
      mulCongr zeroLeft leftInv oneApartEmpty nonzeroOfApartEmpty pa
  have doubleInverse : hsame (inv (inv a pa) pA) a := by
    exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC
      leftId
      rightId
      mulCongr
      (leftInv (inv a pa) pA)
      (leftInv a pa)
  have classifierExact : hsame (inv a pa) (inv b pb) ↔ hsame a b := by
    constructor
    · intro sameInv
      exact field_inverse_cancel_from_apartness
        assocC leftId rightId mulCongr leftInv rightInv pa pb sameInv
    · intro sameAB
      exact field_inverse_congruence_from_apartness
        assocC leftId rightId mulCongr leftInv rightInv sameAB pa pb
  exact Exists.intro pA (And.intro doubleInverse classifierExact)

end BEDC.Derived.FieldUp
