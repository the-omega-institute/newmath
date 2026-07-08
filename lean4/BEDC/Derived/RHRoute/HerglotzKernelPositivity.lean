import BEDC.Derived.RHRoute.JensenTuranDegree2

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.HerglotzKernelPositivity

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

def ratTwoH : Rat :=
  BEDC.Derived.RationalOrderArithUp.ratTwo

def ratFourteen : Rat :=
  ratNat 14

def herglotzRe (num den : Rat) (hden : ratApart0 den) : Rat :=
  ratMul num (ratInvApart den hden)

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratLt_le_trans_local {x y z : Rat} :
    ratLt x y -> ratLe y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) yz
  · intro zx
    exact ratLt_not_ratLe_reverse xy (ratLe_trans yz zx)

private theorem ratLt_add_right_mono_local {x x' y : Rat} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := x) (x' := x') (y := y) (ratLt_to_ratLe h)
  · intro reverse
    have shifted :
        ratLe (ratAdd (ratAdd x' y) (ratNeg y))
          (ratAdd (ratAdd x y) (ratNeg y)) :=
      BEDC.Derived.LocatedReal.ratLe_add_right_mono
        (x := ratAdd x' y) (x' := ratAdd x y) (y := ratNeg y) reverse
    have leftCancel :
        RatEq (ratAdd (ratAdd x' y) (ratNeg y)) x' :=
      RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local x' y (ratNeg y))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x')
            (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
          (ratAdd_zero_right x'))
    have rightCancel :
        RatEq (ratAdd (ratAdd x y) (ratNeg y)) x :=
      RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
          (ratAdd_zero_right x))
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects leftCancel rightCancel shifted)

private theorem ratAdd_pos_of_pos_nonneg {x y : Rat} :
    ratLt ratZero x -> ratLe ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro xPos yNonneg
  have raw : ratLt (ratAdd ratZero y) (ratAdd x y) :=
    ratLt_add_right_mono_local (x := ratZero) (x' := x) (y := y) xPos
  exact ratLe_lt_trans yNonneg
    (ratLt_respects_local (ratZero_add_left y) (RatEq_refl _) raw)

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro xPos yPos
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left yPos xPos
  exact ratLt_respects_local (ratMul_zero_right_local x) (RatEq_refl _) raw

private theorem ratInvApart_pos_of_pos_local {y : Rat}
    (hyPos : ratLt ratZero y) (hyApart : ratApart0 y) :
    ratLt ratZero (ratInvApart y hyApart) := by
  have invNonneg : ratLe ratZero (ratInvApart y hyApart) := by
    have raw :
        ratLe ratZero (ratDivApart ratOne y hyApart) :=
      ratDivApart_nonneg_of_nonneg_pos
        BEDC.Real.RatNumLogEnclosure.ratOne_nonneg hyPos hyApart
    unfold ratDivApart at raw
    exact ratLe_of_RatEq_right raw
      (ratOne_mul_left (ratInvApart y hyApart))
  apply ratLe_not_le_to_ratLt
  · exact invNonneg
  · intro invLeZero
    have invZero : RatEq (ratInvApart y hyApart) ratZero :=
      ratLe_antisymm invLeZero invNonneg
    have productZero :
        RatEq (ratMul y (ratInvApart y hyApart)) ratZero :=
      RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl y) invZero)
        (ratMul_zero_right_local y)
    have oneZero : RatEq ratOne ratZero :=
      RatEq_trans _ _ _
        (RatEq_symm (ratInvApart_mul y hyApart))
        productZero
    exact intApart0_not_zero_pair
      BEDC.Real.RatNumLogEnclosure.ratOne_apart
      (RatEq_zero_num oneZero)

theorem herglotz_num_pos
    (σ β : Rat) (hσ : ratLt ratOne σ) (hβ : ratLe β ratOne) :
    ratLt ratZero (ratSub σ β) := by
  exact sub_pos_of_lt (ratLe_lt_trans hβ hσ)

theorem herglotz_mirror_num_pos
    (σ β : Rat) (hσ : ratLt ratOne σ) (hβ0 : ratLe ratZero β) :
    ratLt ratZero (ratSub (ratAdd σ β) ratOne) := by
  have sigmaLeSigmaBeta : ratLe σ (ratAdd σ β) :=
    BEDC.Real.RatNumLogEnclosure.ratLe_add_nonneg_right σ β hβ0
  have oneLtSigmaBeta : ratLt ratOne (ratAdd σ β) :=
    ratLt_le_trans_local hσ sigmaLeSigmaBeta
  exact sub_pos_of_lt oneLtSigmaBeta

theorem sq_sum_pos_of_left_pos (a b : Rat)
    (ha : ratLt ratZero a) :
    ratLt ratZero (ratAdd (ratMul a a) (ratMul b b)) := by
  have leftPos : ratLt ratZero (ratMul a a) :=
    ratMul_pos_local ha ha
  have rightNonneg : ratLe ratZero (ratMul b b) :=
    BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg b
  exact ratAdd_pos_of_pos_nonneg leftPos rightNonneg

theorem herglotz_re_pos (num den : Rat)
    (hnum : ratLt ratZero num) (hden_pos : ratLt ratZero den)
    (hden : ratApart0 den) :
    ratLt ratZero (herglotzRe num den hden) := by
  unfold herglotzRe
  exact ratMul_pos_local hnum (ratInvApart_pos_of_pos_local hden_pos hden)

theorem zero_contribution_pos
    (σ β γ t : Rat)
    (hσ : ratLt ratOne σ)
    (hβ0 : ratLe ratZero β)
    (hβ1 : ratLe β ratOne) :
    ratLt ratZero (ratSub σ β) ∧
    ratLt ratZero
        (ratAdd
          (ratMul (ratSub σ β) (ratSub σ β))
          (ratMul (ratSub t γ) (ratSub t γ))) := by
  have _betaNonneg : ratLe ratZero β := hβ0
  have numPos : ratLt ratZero (ratSub σ β) :=
    herglotz_num_pos σ β hσ hβ1
  exact ⟨numPos, sq_sum_pos_of_left_pos (ratSub σ β) (ratSub t γ) numPos⟩

theorem zero_mirror_contribution_pos
    (σ β γ t : Rat)
    (hσ : ratLt ratOne σ)
    (hβ0 : ratLe ratZero β) :
    ratLt ratZero (ratSub (ratAdd σ β) ratOne) ∧
      ratLt ratZero
        (ratAdd
          (ratMul (ratSub (ratAdd σ β) ratOne) (ratSub (ratAdd σ β) ratOne))
          (ratMul (ratAdd t γ) (ratAdd t γ))) := by
  have numPos : ratLt ratZero (ratSub (ratAdd σ β) ratOne) :=
    herglotz_mirror_num_pos σ β hσ hβ0
  exact ⟨numPos, sq_sum_pos_of_left_pos (ratSub (ratAdd σ β) ratOne)
    (ratAdd t γ) numPos⟩

theorem concrete_sigma_two_gt_one :
    ratLt ratOne ratTwoH := by
  unfold ratTwoH BEDC.Derived.RationalOrderArithUp.ratTwo
  change ratLt (ratNat 1) (ratNat 2)
  exact BEDC.Real.RatNumLogEnclosure.ratNat_lt_of_nat_lt (Nat.succ_lt_succ (Nat.succ_pos 0))

theorem concrete_half_nonneg :
    ratLe ratZero ratHalf := by
  change ratLe ratZero (ratDivApart ratOne BEDC.Derived.RationalOrderArithUp.ratTwo
    BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
  exact BEDC.Real.RatNumKernel.ratDivApart_nonneg_of_nonneg_pos
    BEDC.Real.RatNumLogEnclosure.ratOne_nonneg
    BEDC.Derived.RationalOrderArithUp.ratTwo_pos
    BEDC.Derived.RationalOrderArithUp.ratTwo_apart

theorem concrete_half_le_one :
    ratLe ratHalf ratOne := by
  change ratLe
    (ratDivApart ratOne BEDC.Derived.RationalOrderArithUp.ratTwo
      BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
    ratOne
  apply ratMul_le_cancel_right BEDC.Derived.RationalOrderArithUp.ratTwo_pos
  have leftCancel :
      RatEq
        (ratMul
          (ratDivApart ratOne BEDC.Derived.RationalOrderArithUp.ratTwo
            BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
          BEDC.Derived.RationalOrderArithUp.ratTwo)
        ratOne := by
    unfold BEDC.Derived.RationalOrderArithUp.ratTwo ratDivApart
    have invMul :
        RatEq
          (ratMul
            (ratInvApart (ratNat 2)
              BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
            (ratNat 2))
          ratOne :=
      RatEq_trans _ _ _
        (ratMul_comm
          (ratInvApart (ratNat 2)
            BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
          (ratNat 2))
        (ratInvApart_mul (ratNat 2)
          BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
    exact RatEq_trans _ _ _
      (ratMul_assoc ratOne
        (ratInvApart (ratNat 2)
          BEDC.Derived.RationalOrderArithUp.ratTwo_apart)
        (ratNat 2))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl ratOne) invMul)
        (ratMul_one_right ratOne))
  have rightEq :
      RatEq (ratMul ratOne BEDC.Derived.RationalOrderArithUp.ratTwo)
        BEDC.Derived.RationalOrderArithUp.ratTwo :=
    ratOne_mul_left BEDC.Derived.RationalOrderArithUp.ratTwo
  exact ratLe_respects leftCancel rightEq
    (ratLt_to_ratLe concrete_sigma_two_gt_one)

theorem concrete_zero_contribution_pos :
    ratLt ratZero (ratSub ratTwoH ratHalf) ∧
      ratLt ratZero
        (ratAdd
          (ratMul (ratSub ratTwoH ratHalf) (ratSub ratTwoH ratHalf))
          (ratMul (ratSub ratFourteen ratFourteen) (ratSub ratFourteen ratFourteen))) :=
  zero_contribution_pos ratTwoH ratHalf ratFourteen ratFourteen
    concrete_sigma_two_gt_one concrete_half_nonneg concrete_half_le_one

theorem concrete_mirror_contribution_pos :
    ratLt ratZero (ratSub (ratAdd ratTwoH ratHalf) ratOne) ∧
      ratLt ratZero
        (ratAdd
          (ratMul (ratSub (ratAdd ratTwoH ratHalf) ratOne)
            (ratSub (ratAdd ratTwoH ratHalf) ratOne))
          (ratMul (ratAdd ratFourteen ratFourteen) (ratAdd ratFourteen ratFourteen))) :=
  zero_mirror_contribution_pos ratTwoH ratHalf ratFourteen ratFourteen
    concrete_sigma_two_gt_one concrete_half_nonneg

end BEDC.Derived.RHRoute.HerglotzKernelPositivity
