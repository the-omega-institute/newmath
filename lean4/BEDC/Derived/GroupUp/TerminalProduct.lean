import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_terminal_package :
    (forall h k : BHist, GroupSingletonClassifier h k <->
      GroupSingletonCarrier h ∧ GroupSingletonCarrier k) ∧
    (forall p q : BHist, GroupSingletonCarrier (append p q) <->
      GroupSingletonCarrier p ∧ GroupSingletonCarrier q) ∧
    (forall h : BHist, GroupSingletonCarrier h ->
      GroupSingletonCarrier BHist.Empty ∧ GroupSingletonClassifier BHist.Empty h ∧
        GroupSingletonClassifier h BHist.Empty) := by
  constructor
  · intro h k
    constructor
    · intro classified
      exact And.intro classified.left classified.right.left
    · intro carriers
      exact And.intro carriers.left
        (And.intro carriers.right (hsame_trans carriers.left (hsame_symm carriers.right)))
  · constructor
    · intro p q
      constructor
      · intro carrier
        exact append_eq_empty_iff.mp carrier
      · intro carriers
        exact append_eq_empty_iff.mpr carriers
    · intro h carrier
      have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
      have emptyLeft : GroupSingletonClassifier BHist.Empty h := by
        exact And.intro emptyCarrier (And.intro carrier (hsame_symm carrier))
      have emptyRight : GroupSingletonClassifier h BHist.Empty := by
        exact And.intro carrier (And.intro emptyCarrier carrier)
      exact And.intro emptyCarrier (And.intro emptyLeft emptyRight)

 theorem group_product_unit_inverse_correspondence_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty) {a b : BHist} :
    (hsame (mul a b) BHist.Empty <-> hsame a (inv b)) ∧
      (hsame (mul a b) BHist.Empty <-> hsame b (inv a)) := by
  constructor
  · constructor
    · intro productUnit
      have raw := (group_right_mul_equation_exact_from_empty_unit assocC rightId mulCongr
        leftInv rightInv).mp productUnit
      exact hsame_trans raw (leftId (inv b))
    · intro sameA
      have lifted : hsame a (mul BHist.Empty (inv b)) :=
        hsame_trans sameA (hsame_symm (leftId (inv b)))
      exact (group_right_mul_equation_exact_from_empty_unit assocC rightId mulCongr
        leftInv rightInv).mpr lifted
  · constructor
    · intro productUnit
      have raw := (group_left_mul_equation_exact_from_empty_unit assocC leftId mulCongr
        leftInv rightInv).mp productUnit
      exact hsame_trans raw (rightId (inv a))
    · intro sameB
      have lifted : hsame b (mul (inv a) BHist.Empty) :=
        hsame_trans sameB (hsame_symm (rightId (inv a)))
      exact (group_left_mul_equation_exact_from_empty_unit assocC leftId mulCongr
        leftInv rightInv).mpr lifted

end BEDC.Derived.GroupUp
