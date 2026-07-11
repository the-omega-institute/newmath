import BEDC.Derived.RHRoute.EulerHasseEtaCenterProduct.RatEncode
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.EulerHasseEtaCenterProduct

open BEDC.Algebra.Rel (RelCommRing)
open BEDC.Derived.RHRoute.EulerHasseEta
open BEDC.Derived.RHRoute.ZetaBoxEvaluator (ratComplexMul)
open BEDC.Derived.RationalUp
  (RatEq intLe intToRat ratZero ratOne ratAdd ratMul ratNeg ratSub
    ratLe ratLeBool RatEq_refl RatEq_symm RatEq_trans ratLe_refl
    ratLe_total ratLe_trans ratLe_respects ratLe_antisymm ratLt_to_ratLe
    ratLt_not_ratLe_reverse ratLe_not_le_to_ratLt ratAdd_respects
    ratMul_respects ratNeg_respects ratAdd_comm ratMul_comm
    ratAdd_zero_right ratZero_add_left ratMul_assoc ratMul_one_right
    ratOne_mul_left ratMul_le_mul_right ratMul_le_mul_left
    ratSub_nonneg_of_le ratDenInt)

private theorem natLeBool_true_to_le_local {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le_local h)

private theorem ratLe_to_ratLeBool {x y : Rat} :
    ratLe x y -> ratLeBool x y = true := by
  intro h
  unfold ratLeBool
  unfold ratLe BEDC.Derived.RationalUp.intLe at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le
    ((BEDC.Derived.IntUp.pairLe_iff_length_order
      (BEDC.Derived.RationalUp.intToPair_carrier _)
      (BEDC.Derived.RationalUp.intToPair_carrier _)).mp h)

private theorem ratMin_le_left (x y : Rat) :
    ratLe (ratMin x y) x := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl x
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool xy] at h
          cases h
      | inr yx =>
          exact yx

private theorem ratMin_le_right (x y : Rat) :
    ratLe (ratMin x y) y := by
  unfold ratMin
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe h
  | false =>
      exact ratLe_refl y

private theorem ratMax_ge_left (x y : Rat) :
    ratLe x (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLeBool_true_to_ratLe h
  | false =>
      exact ratLe_refl x

private theorem ratMax_ge_right (x y : Rat) :
    ratLe y (ratMax x y) := by
  unfold ratMax
  cases h : ratLeBool x y with
  | true =>
      exact ratLe_refl y
  | false =>
      cases ratLe_total x y with
      | inl xy =>
          rw [ratLe_to_ratLeBool xy] at h
          cases h
      | inr yx =>
          exact yx

private theorem foldl_ratMin_le_acc (a _c : Rat) (l : List Rat) :
    ratLe (l.foldl ratMin a) a := by
  induction l generalizing a with
  | nil =>
      exact ratLe_refl a
  | cons x xs ih =>
      exact ratLe_trans (ih (ratMin a x)) (ratMin_le_left a x)

private theorem foldl_ratMin_le_of_mem (a c : Rat) (l : List Rat)
    (h : c ∈ l) :
    ratLe (l.foldl ratMin a) c := by
  induction l generalizing a with
  | nil =>
      cases h
  | cons x xs ih =>
      cases h with
      | head =>
          exact ratLe_trans (foldl_ratMin_le_acc (ratMin a c) c xs)
            (ratMin_le_right a c)
      | tail _ htail =>
          exact ih (ratMin a x) htail

theorem ratListMin_le_of_mem (c : Rat) (l : List Rat) (h : c ∈ l) :
    ratLe (ratListMin l) c := by
  cases l with
  | nil =>
      cases h
  | cons x xs =>
      unfold ratListMin
      cases h with
      | head =>
          exact foldl_ratMin_le_acc c c xs
      | tail _ htail =>
          exact foldl_ratMin_le_of_mem x c xs htail

private theorem acc_le_foldl_ratMax (a _c : Rat) (l : List Rat) :
    ratLe a (l.foldl ratMax a) := by
  induction l generalizing a with
  | nil =>
      exact ratLe_refl a
  | cons x xs ih =>
      exact ratLe_trans (ratMax_ge_left a x) (ih (ratMax a x))

private theorem mem_le_foldl_ratMax (a c : Rat) (l : List Rat)
    (h : c ∈ l) :
    ratLe c (l.foldl ratMax a) := by
  induction l generalizing a with
  | nil =>
      cases h
  | cons x xs ih =>
      cases h with
      | head =>
          exact ratLe_trans (ratMax_ge_right a c)
            (acc_le_foldl_ratMax (ratMax a c) c xs)
      | tail _ htail =>
          exact ih (ratMax a x) htail

theorem le_ratListMax_of_mem (c : Rat) (l : List Rat) (h : c ∈ l) :
    ratLe c (ratListMax l) := by
  cases l with
  | nil =>
      cases h
  | cons x xs =>
      unfold ratListMax
      cases h with
      | head =>
          exact acc_le_foldl_ratMax c c xs
      | tail _ htail =>
          exact mem_le_foldl_ratMax x c xs htail

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul
        (BEDC.Derived.RationalUp.IntMul x.num BEDC.Derived.RationalUp.intZero)
        (ratDenInt ratZero))
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero
        (ratDenInt (ratMul x ratZero)))
  exact BEDC.Derived.RationalUp.IntEq_trans
    (BEDC.Derived.RationalUp.intMul_right_congr
      (BEDC.Derived.RationalUp.intMul_zero_right x.num))
    (BEDC.Derived.RationalUp.IntEq_symm
      (BEDC.Derived.RationalUp.intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private def ratRing : RelCommRing Rat RatEq where
  zero := ratZero
  one := ratOne
  add := ratAdd
  mul := ratMul
  neg := ratNeg
  refl := RatEq_refl
  symm := RatEq_symm
  trans := by
    intro _ _ _
    exact RatEq_trans _ _ _
  add_congr := by
    intro _ _ _ _ hleft hright
    exact ratAdd_respects hleft hright
  mul_congr := by
    intro _ _ _ _ hleft hright
    exact ratMul_respects hleft hright
  neg_congr := by
    intro _ _ h
    exact ratNeg_respects h
  add_assoc := BEDC.Derived.LocatedReal.ratAdd_assoc_local
  add_comm := ratAdd_comm
  add_zero := ratAdd_zero_right
  zero_add := ratZero_add_left
  add_neg := BEDC.Derived.LocatedReal.ratAdd_neg_local
  neg_add := BEDC.Derived.LocatedReal.ratNeg_add_local
  mul_assoc := ratMul_assoc
  mul_one := ratMul_one_right
  one_mul := ratOne_mul_left
  mul_zero := ratMul_zero_right_local
  zero_mul := ratMul_zero_left_local
  left_distrib := BEDC.Real.RatNumKernel.ratMul_add_left
  right_distrib := BEDC.Real.RatNumKernel.ratMul_add_right
  mul_comm := ratMul_comm

private theorem ratLe_neg_anti {a b : Rat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local
          a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b)
        (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratNeg_nonneg_of_nonpos {x : Rat} :
    ratLe x ratZero -> ratLe ratZero (ratNeg x) := by
  intro h
  have subNonneg : ratLe ratZero (ratSub ratZero x) :=
    ratSub_nonneg_of_le h
  exact ratLe_respects (RatEq_refl _)
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x) subNonneg

private theorem ratMul_le_mul_right_nonpos {a b c : Rat} :
    ratLe a b -> ratLe c ratZero ->
      ratLe (ratMul b c) (ratMul a c) := by
  intro hab hc
  have negNonneg : ratLe ratZero (ratNeg c) :=
    ratNeg_nonneg_of_nonpos hc
  have scaled :
      ratLe (ratMul a (ratNeg c)) (ratMul b (ratNeg c)) :=
    ratMul_le_mul_right hab negNonneg
  have negScaled :
      ratLe (ratNeg (ratMul a c)) (ratNeg (ratMul b c)) :=
    ratLe_respects (ratRing.mul_neg a c) (ratRing.mul_neg b c) scaled
  have raw :
      ratLe (ratNeg (ratNeg (ratMul b c)))
        (ratNeg (ratNeg (ratMul a c))) :=
    ratLe_neg_anti negScaled
  exact ratLe_respects
    (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul b c))
    (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul a c))
    raw

private theorem ratMul_le_mul_left_nonpos {a b c : Rat} :
    ratLe a b -> ratLe c ratZero ->
      ratLe (ratMul c b) (ratMul c a) := by
  intro hab hc
  exact ratLe_respects
    (ratMul_comm b c)
    (ratMul_comm a c)
    (ratMul_le_mul_right_nonpos hab hc)

private theorem eta_re_hi_nonpos :
    ratLe EtaCBox.re.hi ratZero := by
  change ratLe (q (-2) 1000000) (q 0 1)
  exact etaCBox_re_hi_nonpos

private theorem eta_im_hi_nonpos :
    ratLe EtaCBox.im.hi ratZero := by
  change ratLe (q (-47) 1000000) (q 0 1)
  exact etaCBox_im_hi_nonpos

private theorem invD_re_lo_nonneg :
    ratLe ratZero InvDBoxC.re.lo := by
  change ratLe (q 0 1) (q 257 625)
  exact invDBoxC_re_lo_nonneg

private theorem invD_re_hi_nonneg :
    ratLe ratZero InvDBoxC.re.hi := by
  change ratLe (q 0 1) (q 4113 10000)
  exact invDBoxC_re_hi_nonneg

private theorem invD_im_lo_nonneg :
    ratLe ratZero InvDBoxC.im.lo := by
  change ratLe (q 0 1) (q 913 10000)
  exact invDBoxC_im_lo_nonneg

private theorem invD_im_hi_nonneg :
    ratLe ratZero InvDBoxC.im.hi := by
  change ratLe (q 0 1) (q 183 2000)
  exact invDBoxC_im_hi_nonneg

theorem zeta_center_box_from_eta_invD_discharge :
    EulerHasseEta.zeta_center_box_from_eta_invD_obligation := by
  intro eta invD he hi
  constructor
  · have reLowerMul :
        ratLe (ratMul EtaCBox.re.lo InvDBoxC.re.hi)
          (ratMul eta.re invD.re) := by
      have etaReNonpos : ratLe eta.re ratZero :=
        ratLe_trans he.left.right eta_re_hi_nonpos
      exact ratLe_trans
        (ratMul_le_mul_right he.left.left invD_re_hi_nonneg)
        (ratMul_le_mul_left_nonpos hi.left.right etaReNonpos)
    have imUpperMul :
        ratLe (ratMul eta.im invD.im)
          (ratMul EtaCBox.im.hi InvDBoxC.im.lo) := by
      have invDImNonneg : ratLe ratZero invD.im :=
        ratLe_trans invD_im_lo_nonneg hi.right.left
      exact ratLe_trans
        (ratMul_le_mul_right he.right.right invDImNonneg)
        (ratMul_le_mul_left_nonpos hi.right.left eta_im_hi_nonpos)
    have negImLower :
        ratLe (ratNeg (ratMul EtaCBox.im.hi InvDBoxC.im.lo))
          (ratNeg (ratMul eta.im invD.im)) :=
      ratLe_neg_anti imUpperMul
    have lowerSum :
        ratLe
          (ratAdd (ratMul EtaCBox.re.lo InvDBoxC.re.hi)
            (ratNeg (ratMul EtaCBox.im.hi InvDBoxC.im.lo)))
          (ratAdd (ratMul eta.re invD.re)
            (ratNeg (ratMul eta.im invD.im))) :=
      BEDC.Real.RatNumKernel.ratAdd_le_add reLowerMul negImLower
    have zetaFits :
        ratLe ZetaCBox.re.lo
          (ratAdd (ratMul EtaCBox.re.lo InvDBoxC.re.hi)
            (ratNeg (ratMul EtaCBox.im.hi InvDBoxC.im.lo))) := by
      change ratLe (q 3 1000000)
        (ratAdd (ratMul (q (-3) 1000000) (q 4113 10000))
          (ratNeg (ratMul (q (-47) 1000000) (q 913 10000))))
      exact centerProduct_re_lower_fits
    constructor
    · exact ratLe_trans zetaFits lowerSum
    · have reUpperMul :
          ratLe (ratMul eta.re invD.re)
            (ratMul EtaCBox.re.hi InvDBoxC.re.lo) := by
        have invDReNonneg : ratLe ratZero invD.re :=
          ratLe_trans invD_re_lo_nonneg hi.left.left
        exact ratLe_trans
          (ratMul_le_mul_right he.left.right invDReNonneg)
          (ratMul_le_mul_left_nonpos hi.left.left eta_re_hi_nonpos)
      have imLowerMul :
          ratLe (ratMul EtaCBox.im.lo InvDBoxC.im.hi)
            (ratMul eta.im invD.im) := by
        have etaImNonpos : ratLe eta.im ratZero :=
          ratLe_trans he.right.right eta_im_hi_nonpos
        exact ratLe_trans
          (ratMul_le_mul_right he.right.left invD_im_hi_nonneg)
          (ratMul_le_mul_left_nonpos hi.right.right etaImNonpos)
      have negImUpper :
          ratLe (ratNeg (ratMul eta.im invD.im))
            (ratNeg (ratMul EtaCBox.im.lo InvDBoxC.im.hi)) :=
        ratLe_neg_anti imLowerMul
      have upperSum :
          ratLe
            (ratAdd (ratMul eta.re invD.re)
              (ratNeg (ratMul eta.im invD.im)))
            (ratAdd (ratMul EtaCBox.re.hi InvDBoxC.re.lo)
              (ratNeg (ratMul EtaCBox.im.lo InvDBoxC.im.hi))) :=
        BEDC.Real.RatNumKernel.ratAdd_le_add reUpperMul negImUpper
      have zetaFits :
          ratLe
            (ratAdd (ratMul EtaCBox.re.hi InvDBoxC.re.lo)
              (ratNeg (ratMul EtaCBox.im.lo InvDBoxC.im.hi)))
            ZetaCBox.re.hi := by
        change ratLe
          (ratAdd (ratMul (q (-2) 1000000) (q 257 625))
            (ratNeg (ratMul (q (-48) 1000000) (q 183 2000))))
          (q 4 1000000)
        exact centerProduct_re_upper_fits
      exact ratLe_trans upperSum zetaFits
  · have reLowerMul :
        ratLe (ratMul EtaCBox.re.lo InvDBoxC.im.hi)
          (ratMul eta.re invD.im) := by
      have etaReNonpos : ratLe eta.re ratZero :=
        ratLe_trans he.left.right eta_re_hi_nonpos
      exact ratLe_trans
        (ratMul_le_mul_right he.left.left invD_im_hi_nonneg)
        (ratMul_le_mul_left_nonpos hi.right.right etaReNonpos)
    have imLowerMul :
        ratLe (ratMul EtaCBox.im.lo InvDBoxC.re.hi)
          (ratMul eta.im invD.re) := by
      have etaImNonpos : ratLe eta.im ratZero :=
        ratLe_trans he.right.right eta_im_hi_nonpos
      exact ratLe_trans
        (ratMul_le_mul_right he.right.left invD_re_hi_nonneg)
        (ratMul_le_mul_left_nonpos hi.left.right etaImNonpos)
    have lowerSum :
        ratLe
          (ratAdd (ratMul EtaCBox.re.lo InvDBoxC.im.hi)
            (ratMul EtaCBox.im.lo InvDBoxC.re.hi))
          (ratAdd (ratMul eta.re invD.im)
            (ratMul eta.im invD.re)) :=
      BEDC.Real.RatNumKernel.ratAdd_le_add reLowerMul imLowerMul
    have zetaFits :
        ratLe ZetaCBox.im.lo
          (ratAdd (ratMul EtaCBox.re.lo InvDBoxC.im.hi)
            (ratMul EtaCBox.im.lo InvDBoxC.re.hi)) := by
      change ratLe (q (-21) 1000000)
        (ratAdd (ratMul (q (-3) 1000000) (q 183 2000))
          (ratMul (q (-48) 1000000) (q 4113 10000)))
      exact centerProduct_im_lower_fits
    constructor
    · exact ratLe_trans zetaFits lowerSum
    · have reUpperMul :
          ratLe (ratMul eta.re invD.im)
            (ratMul EtaCBox.re.hi InvDBoxC.im.lo) := by
        have invDImNonneg : ratLe ratZero invD.im :=
          ratLe_trans invD_im_lo_nonneg hi.right.left
        exact ratLe_trans
          (ratMul_le_mul_right he.left.right invDImNonneg)
          (ratMul_le_mul_left_nonpos hi.right.left eta_re_hi_nonpos)
      have imUpperMul :
          ratLe (ratMul eta.im invD.re)
            (ratMul EtaCBox.im.hi InvDBoxC.re.lo) := by
        have invDReNonneg : ratLe ratZero invD.re :=
          ratLe_trans invD_re_lo_nonneg hi.left.left
        exact ratLe_trans
          (ratMul_le_mul_right he.right.right invDReNonneg)
          (ratMul_le_mul_left_nonpos hi.left.left eta_im_hi_nonpos)
      have upperSum :
          ratLe
            (ratAdd (ratMul eta.re invD.im)
              (ratMul eta.im invD.re))
            (ratAdd (ratMul EtaCBox.re.hi InvDBoxC.im.lo)
              (ratMul EtaCBox.im.hi InvDBoxC.re.lo)) :=
        BEDC.Real.RatNumKernel.ratAdd_le_add reUpperMul imUpperMul
      have zetaFits :
          ratLe
            (ratAdd (ratMul EtaCBox.re.hi InvDBoxC.im.lo)
              (ratMul EtaCBox.im.hi InvDBoxC.re.lo))
            ZetaCBox.im.hi := by
        change ratLe
          (ratAdd (ratMul (q (-2) 1000000) (q 913 10000))
            (ratMul (q (-47) 1000000) (q 257 625)))
          (q (-19) 1000000)
        exact centerProduct_im_upper_fits
      exact ratLe_trans upperSum zetaFits

theorem zetaCenterBox_discharged :
    ∀ {eta invD : EulerHasseEta.RatComplex},
      InRect eta EtaCBox ->
        InRect invD InvDBoxC ->
          InRect (ratComplexMul eta invD) ZetaCBox :=
  @zeta_center_box_from_eta_invD_discharge

end BEDC.Derived.RHRoute.EulerHasseEtaCenterProduct
