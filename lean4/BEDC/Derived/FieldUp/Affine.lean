import BEDC.Derived.FieldUp
import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

 theorem field_affine_two_sided_equation_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulLeftId : forall x : BHist, hsame (mul one x) x)
    (mulRightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (mulLeftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (mulRightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x d c : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (add (mul (mul a x) b) d) c <->
      hsame x (mul (inv a pa) (mul (add c (neg d)) (inv b pb))) := by
  constructor
  · intro sameAffine
    have offsetTransport :
        hsame (add (add (mul (mul a x) b) d) (neg d)) (add c (neg d)) := by
      exact addCongr sameAffine (hsame_refl (neg d))
    have collapseOffset :
        hsame (add (add (mul (mul a x) b) d) (neg d)) (mul (mul a x) b) := by
      exact hsame_trans (addAssoc (mul (mul a x) b) d (neg d))
        (hsame_trans (addCongr (hsame_refl (mul (mul a x) b)) (negRight d))
          (addRightId (mul (mul a x) b)))
    have middleEquation :
        hsame (mul (mul a x) b) (add c (neg d)) := by
      exact hsame_trans (hsame_symm collapseOffset) offsetTransport
    exact
      (field_middle_mul_equation_exact_from_apartness
        mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv pa pb).mp
        middleEquation
  · intro sameSolution
    have middleEquation :
        hsame (mul (mul a x) b) (add c (neg d)) := by
      exact
        (field_middle_mul_equation_exact_from_apartness
          mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv pa pb).mpr
          sameSolution
    have offsetTransport :
        hsame (add (mul (mul a x) b) d) (add (add c (neg d)) d) := by
      exact addCongr middleEquation (hsame_refl d)
    have collapseOffset : hsame (add (add c (neg d)) d) c := by
      exact hsame_trans (addAssoc c (neg d) d)
        (hsame_trans (addCongr (hsame_refl c) (negLeft d)) (addRightId c))
    exact hsame_trans offsetTransport collapseOffset

 theorem field_affine_two_sided_map_classifier_exact_from_apartness
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (mulAssoc : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (mulLeftId : forall x : BHist, hsame (mul one x) x)
    (mulRightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (mulLeftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (mulRightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b x y d : BHist} (pa : NonZero a) (pb : NonZero b) :
    hsame (add (mul (mul a x) b) d) (add (mul (mul a y) b) d) <->
      hsame x y := by
  constructor
  · intro sameAffine
    have sameProducts :
        hsame (mul (mul a x) b) (mul (mul a y) b) := by
      exact
        BEDC.Derived.GroupUp.group_right_cancel
          (mul := add) (e := BHist.Empty) (inv := neg)
          addAssoc addRightId addCongr negRight sameAffine
    exact
      (field_two_sided_mul_exact_from_apartness
        mulAssoc mulLeftId mulRightId mulCongr mulLeftInv mulRightInv pa pb).mp
        sameProducts
  · intro sameMiddle
    exact addCongr (mulCongr (mulCongr (hsame_refl a) sameMiddle) (hsame_refl b))
      (hsame_refl d)

end BEDC.Derived.FieldUp
