import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_affine_automorphism_cancellation_exact_from_empty_unit_group_laws_iff
    {comp : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (comp (comp x y) z) (comp x (comp y z)))
    (leftId : forall x : BHist, hsame (comp BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (comp x BHist.Empty) x)
    (compCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (comp a b) (comp a' b'))
    (leftInv : forall x : BHist, hsame (comp (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (comp x (inv x)) BHist.Empty)
    {S T U : BHist} :
    (hsame (comp S T) (comp U T) <-> hsame S U) ∧
      (hsame (comp T S) (comp T U) <-> hsame S U) := by
  constructor
  · constructor
    · intro sameRightProducts
      exact BEDC.Derived.GroupUp.group_right_cancel
        (mul := comp) (e := BHist.Empty) (inv := inv)
        assocC rightId compCongr rightInv sameRightProducts
    · intro sameSU
      exact compCongr sameSU (hsame_refl T)
  · constructor
    · intro sameLeftProducts
      exact BEDC.Derived.GroupUp.group_left_cancel
        (mul := comp) (e := BHist.Empty) (inv := inv)
        assocC leftId compCongr leftInv sameLeftProducts
    · intro sameSU
      exact compCongr (hsame_refl T) sameSU

end BEDC.Derived.FieldUp
