import BEDC.Derived.RHRoute.IntervalMatrixPSD.AlgebraNormalize
import BEDC.Derived.RationalOrderArithUp
import BEDC.Real.RatNumLogEnclosure

namespace BEDC.Derived.RHRoute.JensenTuranDegree2

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

abbrev Rat : Type :=
  RatNum

def ratTwoJ : Rat :=
  ratAdd ratOne ratOne

def jensen2 (a b c X : Rat) : Rat :=
  ratAdd
    (ratAdd a (ratMul (ratMul ratTwoJ b) X))
    (ratMul c (ratMul X X))

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

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratSub_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem ratSub_mul_left_local (c a b : Rat) :
    RatEq (ratMul c (ratSub a b))
      (ratSub (ratMul c a) (ratMul c b)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_left c a (ratNeg b))
    (ratAdd_respects (RatEq_refl (ratMul c a))
      (ratMul_neg_right_local c b))

private abbrev ratRing : BEDC.Algebra.Rel.RelCommRing Rat RatEq :=
  BEDC.Derived.RHRoute.IntervalMatrixPSD.ratRelCommRing

private theorem ratNeg_pos_of_neg {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratNeg x) := by
  intro h
  have subPos : ratLt ratZero (ratSub ratZero x) :=
    sub_pos_of_lt h
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    subPos
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

theorem ratMul_self_nonneg (x : Rat) :
    ratLe ratZero (ratMul x x) := by
  cases rat_order_trichotomy ratZero x with
  | inl xPos =>
      exact BEDC.Real.RatNumKernel.ratMul_nonneg
        (ratLt_to_ratLe xPos) (ratLt_to_ratLe xPos)
  | inr rest =>
      cases rest with
      | inl xZero =>
          have squareZero : RatEq (ratMul x x) ratZero := by
            exact RatEq_trans _ _ _
              (ratMul_respects (RatEq_symm xZero) (RatEq_symm xZero))
              (ratMul_zero_left_local ratZero)
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            (ratLe_refl ratZero) (RatEq_symm squareZero)
      | inr xNeg =>
          have negNonneg : ratLe ratZero (ratNeg x) :=
            ratLt_to_ratLe (ratNeg_pos_of_neg xNeg)
          have negSquareNonneg :
              ratLe ratZero (ratMul (ratNeg x) (ratNeg x)) :=
            BEDC.Real.RatNumKernel.ratMul_nonneg negNonneg negNonneg
          have sameSquare :
              RatEq (ratMul (ratNeg x) (ratNeg x)) (ratMul x x) :=
            ratRing.neg_neg_mul_neg x x
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            negSquareNonneg sameSquare

private theorem ratAdd_nonneg_local {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratAdd_ge_right_of_left_nonneg {x y : Rat} :
    ratLe ratZero x -> ratLe y (ratAdd x y) := by
  intro hx
  have raw :
      ratLe (ratAdd ratZero y) (ratAdd x y) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratZero) (x' := x) (y := y) hx
  exact ratLe_respects (ratZero_add_left y) (RatEq_refl _) raw

private theorem ratMul_le_cancel_left_pos {a b c : Rat} :
    ratLt ratZero c -> ratLe (ratMul c a) (ratMul c b) -> ratLe a b := by
  intro hc h
  have swapped :
      ratLe (ratMul a c) (ratMul b c) :=
    ratLe_respects (ratMul_comm c a) (ratMul_comm c b) h
  exact ratMul_le_cancel_right hc swapped

private theorem ratLe_of_mul_left_nonpos_pos {c x : Rat} :
    ratLt ratZero c -> ratLe (ratMul c x) ratZero -> ratLe x ratZero := by
  intro hc h
  have h' : ratLe (ratMul c x) (ratMul c ratZero) :=
    BEDC.Real.RatNumKernel.ratLe_of_RatEq_right h
      (RatEq_symm (ratMul_zero_right_local c))
  exact ratMul_le_cancel_left_pos hc h'

private theorem ratAdd_sub_cancel_left_local (x y : Rat) :
    RatEq (ratAdd y (ratSub x y)) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (RatEq_symm
      (BEDC.Derived.LocatedReal.ratAdd_assoc_local y x (ratNeg y)))
    (RatEq_trans _ _ _
      (ratAdd_respects (ratAdd_comm y x) (RatEq_refl (ratNeg y)))
      (RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl x)
            (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
          (ratAdd_zero_right x))))

private theorem ratLe_of_sub_nonneg_local {x y : Rat} :
    ratLe ratZero (ratSub x y) -> ratLe y x := by
  intro h
  have raw :
      ratLe (ratAdd y ratZero) (ratAdd y (ratSub x y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (y := ratZero) (y' := ratSub x y) (x := y) h
  exact ratLe_respects
    (ratAdd_zero_right y)
    (ratAdd_sub_cancel_left_local x y)
    raw

private theorem ratSub_le_zero_of_le_local {x y : Rat} :
    ratLe x y -> ratLe (ratSub x y) ratZero := by
  intro h
  cases ratLe_total (ratSub x y) ratZero with
  | inl subNonpos => exact subNonpos
  | inr subNonneg =>
      have yLeX : ratLe y x :=
        ratLe_of_sub_nonneg_local subNonneg
      have same : RatEq x y :=
        ratLe_antisymm h yLeX
      exact ratLe_of_RatEq ((ratSub_zero_iff x y).mpr same)

private theorem ratLe_of_sub_le_zero_local {x y : Rat} :
    ratLe (ratSub x y) ratZero -> ratLe x y := by
  intro h
  cases ratLe_total x y with
  | inl xy => exact xy
  | inr yx =>
      have subNonneg : ratLe ratZero (ratSub x y) :=
        ratSub_nonneg_of_le yx
      have subZero : RatEq (ratSub x y) ratZero :=
        ratLe_antisymm h subNonneg
      exact ratLe_of_RatEq ((ratSub_zero_iff x y).mp subZero)

private theorem jensen2_witness_linear_zero
    (b c : Rat) (hca : ratApart0 c) :
    RatEq
      (ratAdd
        (ratMul c (ratMul (ratNeg b) (ratInvApart c hca)))
        b)
      ratZero := by
  let inv := ratInvApart c hca
  have regroup :
      RatEq
        (ratMul c (ratMul (ratNeg b) inv))
        (ratMul (ratNeg b) (ratMul c inv)) := by
    exact RatEq_trans _ _ _
      (RatEq_symm (ratMul_assoc c (ratNeg b) inv))
      (RatEq_trans _ _ _
        (ratMul_respects (ratMul_comm c (ratNeg b)) (RatEq_refl inv))
        (ratMul_assoc (ratNeg b) c inv))
  have cInvOne : RatEq (ratMul c inv) ratOne :=
    ratInvApart_mul c hca
  have prod :
      RatEq
        (ratMul c (ratMul (ratNeg b) inv))
        (ratNeg b) :=
    RatEq_trans _ _ _ regroup
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratNeg b)) cInvOne)
        (ratMul_one_right (ratNeg b)))
  exact RatEq_trans _ _ _
    (ratAdd_respects prod (RatEq_refl b))
    (BEDC.Derived.LocatedReal.ratNeg_add_local b)

theorem jensen2_complete_square (a b c X : Rat) :
    RatEq
      (ratMul c (jensen2 a b c X))
      (ratAdd
        (ratMul (ratAdd (ratMul c X) b) (ratAdd (ratMul c X) b))
        (ratSub (ratMul a c) (ratMul b b))) := by
  have bridge :=
    BEDC.Derived.RHRoute.IntervalMatrixPSD.complete_square_identity
      c b a X ratOne
  change
    RatEq
      (ratMul c
        (ratAdd
          (ratAdd
            (ratMul c (ratMul X X))
            (ratMul (ratMul (ratAdd ratOne ratOne) b)
              (ratMul X ratOne)))
          (ratMul a (ratMul ratOne ratOne))))
      (ratAdd
        (ratMul
          (ratAdd (ratMul c X) (ratMul b ratOne))
          (ratAdd (ratMul c X) (ratMul b ratOne)))
        (ratMul
          (ratSub (ratMul c a) (ratMul b b))
          (ratMul ratOne ratOne))) at bridge
  have leftPoly :
      RatEq
        (ratAdd
          (ratAdd a (ratMul (ratMul ratTwoJ b) X))
          (ratMul c (ratMul X X)))
        (ratAdd
          (ratAdd
            (ratMul c (ratMul X X))
            (ratMul (ratMul (ratAdd ratOne ratOne) b)
              (ratMul X ratOne)))
          (ratMul a (ratMul ratOne ratOne))) := by
    have mid :
        RatEq (ratMul (ratMul ratTwoJ b) X)
          (ratMul (ratMul (ratAdd ratOne ratOne) b) (ratMul X ratOne)) := by
      unfold ratTwoJ
      exact RatEq_symm
        (ratMul_respects (RatEq_refl (ratMul (ratAdd ratOne ratOne) b))
          (ratMul_one_right X))
    have tail :
        RatEq (ratMul a (ratMul ratOne ratOne)) a := by
      exact RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl a) (ratOne_mul_left ratOne))
        (ratMul_one_right a)
    have step1 :
        RatEq
          (ratAdd
            (ratAdd a (ratMul (ratMul ratTwoJ b) X))
            (ratMul c (ratMul X X)))
          (ratAdd
            (ratAdd (ratMul c (ratMul X X)) a)
            (ratMul (ratMul ratTwoJ b) X)) := by
      exact RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a
          (ratMul (ratMul ratTwoJ b) X) (ratMul c (ratMul X X)))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl a)
            (ratAdd_comm (ratMul (ratMul ratTwoJ b) X)
              (ratMul c (ratMul X X))))
          (RatEq_trans _ _ _
            (RatEq_symm
              (BEDC.Derived.LocatedReal.ratAdd_assoc_local a
                (ratMul c (ratMul X X))
                (ratMul (ratMul ratTwoJ b) X)))
            (ratAdd_respects
              (ratAdd_comm a (ratMul c (ratMul X X)))
              (RatEq_refl (ratMul (ratMul ratTwoJ b) X)))))
    have step2 :
        RatEq
          (ratAdd
            (ratAdd (ratMul c (ratMul X X)) a)
            (ratMul (ratMul ratTwoJ b) X))
          (ratAdd
            (ratAdd (ratMul c (ratMul X X))
              (ratMul (ratMul ratTwoJ b) X))
            a) := by
      exact RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (ratMul c (ratMul X X)) a (ratMul (ratMul ratTwoJ b) X))
        (RatEq_trans _ _ _
          (ratAdd_respects (RatEq_refl (ratMul c (ratMul X X)))
            (ratAdd_comm a (ratMul (ratMul ratTwoJ b) X)))
          (RatEq_symm
            (BEDC.Derived.LocatedReal.ratAdd_assoc_local
              (ratMul c (ratMul X X))
              (ratMul (ratMul ratTwoJ b) X) a)))
    exact RatEq_trans _ _ _ step1
      (RatEq_trans _ _ _ step2
        (ratAdd_respects
          (ratAdd_respects (RatEq_refl (ratMul c (ratMul X X))) mid)
          (RatEq_symm tail)))
  have left :
      RatEq
        (ratMul c (jensen2 a b c X))
        (ratMul c
          (ratAdd
            (ratAdd
              (ratMul c (ratMul X X))
              (ratMul (ratMul (ratAdd ratOne ratOne) b)
                (ratMul X ratOne)))
            (ratMul a (ratMul ratOne ratOne)))) := by
    unfold jensen2
    exact ratMul_respects (RatEq_refl c) leftPoly
  have right :
      RatEq
        (ratAdd
          (ratMul
            (ratAdd (ratMul c X) (ratMul b ratOne))
            (ratAdd (ratMul c X) (ratMul b ratOne)))
          (ratMul
            (ratSub (ratMul c a) (ratMul b b))
            (ratMul ratOne ratOne)))
        (ratAdd
          (ratMul (ratAdd (ratMul c X) b) (ratAdd (ratMul c X) b))
          (ratSub (ratMul a c) (ratMul b b))) := by
    have lin :
        RatEq (ratAdd (ratMul c X) (ratMul b ratOne))
          (ratAdd (ratMul c X) b) :=
      ratAdd_respects (RatEq_refl (ratMul c X)) (ratMul_one_right b)
    have det :
        RatEq (ratSub (ratMul c a) (ratMul b b))
          (ratSub (ratMul a c) (ratMul b b)) :=
      ratSub_respects_local (ratMul_comm c a) (RatEq_refl (ratMul b b))
    have detOne :
        RatEq
          (ratMul
            (ratSub (ratMul c a) (ratMul b b))
            (ratMul ratOne ratOne))
          (ratSub (ratMul a c) (ratMul b b)) := by
      exact RatEq_trans _ _ _
        (ratMul_respects det (ratOne_mul_left ratOne))
        (ratMul_one_right (ratSub (ratMul a c) (ratMul b b)))
    exact ratAdd_respects (ratMul_respects lin lin) detOne
  exact RatEq_trans _ _ _ left
    (RatEq_trans _ _ _ bridge right)

private theorem jensen2_det_le_cP (a b c X : Rat) :
    ratLe
      (ratSub (ratMul a c) (ratMul b b))
      (ratMul c (jensen2 a b c X)) := by
  let lin := ratAdd (ratMul c X) b
  have square_nonneg : ratLe ratZero (ratMul lin lin) :=
    ratMul_self_nonneg lin
  have det_le_rhs :
      ratLe (ratSub (ratMul a c) (ratMul b b))
        (ratAdd (ratMul lin lin) (ratSub (ratMul a c) (ratMul b b))) :=
    ratAdd_ge_right_of_left_nonneg square_nonneg
  exact ratLe_respects (RatEq_refl _)
    (RatEq_symm (jensen2_complete_square a b c X))
    det_le_rhs

private theorem jensen2_cP_nonpos_of_nonpos
    (a b c X : Rat)
    (hc : ratLt ratZero c)
    (hP : ratLe (jensen2 a b c X) ratZero) :
    ratLe (ratMul c (jensen2 a b c X)) ratZero := by
  have scaled :
      ratLe (ratMul c (jensen2 a b c X)) (ratMul c ratZero) :=
    ratMul_le_mul_left hP (ratLt_to_ratLe hc)
  exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right scaled
    (ratMul_zero_right_local c)

theorem jensen2_nonpos_forces_turan
    (a b c X : Rat)
    (hc : ratLt ratZero c)
    (hP : ratLe (jensen2 a b c X) ratZero) :
    ratLe (ratMul a c) (ratMul b b) := by
  have det_le_cP :
      ratLe (ratSub (ratMul a c) (ratMul b b))
        (ratMul c (jensen2 a b c X)) :=
    jensen2_det_le_cP a b c X
  have cP_le_zero :
      ratLe (ratMul c (jensen2 a b c X)) ratZero :=
    jensen2_cP_nonpos_of_nonpos a b c X hc hP
  have det_nonpos :
      ratLe (ratSub (ratMul a c) (ratMul b b)) ratZero :=
    ratLe_trans det_le_cP cP_le_zero
  exact ratLe_of_sub_le_zero_local det_nonpos

private theorem jensen2_rhs_nonpos_at_witness
    (a b c : Rat)
    (hca : ratApart0 c)
    (hT : ratLe (ratMul a c) (ratMul b b)) :
    ratLe
      (ratAdd
        (ratMul
          (ratAdd
            (ratMul c (ratMul (ratNeg b) (ratInvApart c hca)))
            b)
          (ratAdd
            (ratMul c (ratMul (ratNeg b) (ratInvApart c hca)))
            b))
        (ratSub (ratMul a c) (ratMul b b)))
      ratZero := by
  let X0 := ratMul (ratNeg b) (ratInvApart c hca)
  let lin := ratAdd (ratMul c X0) b
  have linZero : RatEq lin ratZero :=
    jensen2_witness_linear_zero b c hca
  have squareZero : RatEq (ratMul lin lin) ratZero := by
    exact RatEq_trans _ _ _
      (ratMul_respects linZero linZero)
      (ratMul_zero_left_local ratZero)
  have detNonpos :
      ratLe (ratSub (ratMul a c) (ratMul b b)) ratZero :=
    ratSub_le_zero_of_le_local hT
  have zeroAddNonpos :
      ratLe
        (ratAdd ratZero (ratSub (ratMul a c) (ratMul b b)))
        ratZero :=
    ratLe_respects
      (RatEq_symm (ratZero_add_left (ratSub (ratMul a c) (ratMul b b))))
      (RatEq_refl ratZero)
      detNonpos
  exact ratLe_respects
    (ratAdd_respects (RatEq_symm squareZero)
      (RatEq_refl (ratSub (ratMul a c) (ratMul b b))))
    (RatEq_refl ratZero)
    zeroAddNonpos

private theorem jensen2_cP_nonpos_of_rhs_nonpos
    (a b c X : Rat)
    (rhsNonpos :
      ratLe
        (ratAdd
          (ratMul
            (ratAdd (ratMul c X) b)
            (ratAdd (ratMul c X) b))
          (ratSub (ratMul a c) (ratMul b b)))
        ratZero) :
    ratLe (ratMul c (jensen2 a b c X)) ratZero := by
  exact ratLe_respects
    (RatEq_symm (jensen2_complete_square a b c X))
    (RatEq_refl ratZero)
    rhsNonpos

theorem jensen2_turan_dips
    (a b c : Rat)
    (hc : ratLt ratZero c)
    (hca : ratApart0 c)
    (hT : ratLe (ratMul a c) (ratMul b b)) :
    ratLe
      (jensen2 a b c (ratMul (ratNeg b) (ratInvApart c hca)))
      ratZero := by
  exact ratLe_of_mul_left_nonpos_pos hc
    (jensen2_cP_nonpos_of_rhs_nonpos a b c
      (ratMul (ratNeg b) (ratInvApart c hca))
      (jensen2_rhs_nonpos_at_witness a b c hca hT))

theorem jensen2_dips_iff_turan
    (a b c : Rat)
    (hc : ratLt ratZero c)
    (hca : ratApart0 c) :
    (∃ X, ratLe (jensen2 a b c X) ratZero) ↔
      ratLe (ratMul a c) (ratMul b b) := by
  constructor
  · intro h
    cases h with
    | intro X hP =>
        exact jensen2_nonpos_forces_turan a b c X hc hP
  · intro hT
    exact ⟨ratMul (ratNeg b) (ratInvApart c hca),
      jensen2_turan_dips a b c hc hca hT⟩

theorem jensen2_two_slope_dips :
    ∃ X, ratLe (jensen2 ratOne ratTwoJ ratOne X) ratZero := by
  have turan :
      ratLe (ratMul ratOne ratOne) (ratMul ratTwoJ ratTwoJ) := by
    apply BEDC.Real.RatNumLogEnclosure.ratLeBool_true_to_ratLe
    rfl
  exact
    (jensen2_dips_iff_turan ratOne ratTwoJ ratOne
      BEDC.Real.RatNumLogEnclosure.ratOne_pos
      BEDC.Real.RatNumLogEnclosure.ratOne_apart).mpr turan

theorem jensen2_unit_bowl_has_no_dip :
    ¬ (∃ X, ratLe (jensen2 ratOne ratZero ratOne X) ratZero) := by
  intro dip
  have turan :
      ratLe (ratMul ratOne ratOne) (ratMul ratZero ratZero) :=
    (jensen2_dips_iff_turan ratOne ratZero ratOne
      BEDC.Real.RatNumLogEnclosure.ratOne_pos
      BEDC.Real.RatNumLogEnclosure.ratOne_apart).mp dip
  have oneMul : RatEq (ratMul ratOne ratOne) ratOne :=
    ratMul_one_right ratOne
  have zeroMul : RatEq (ratMul ratZero ratZero) ratZero :=
    ratMul_zero_left_local ratZero
  have oneLeZero : ratLe ratOne ratZero :=
    ratLe_respects oneMul zeroMul turan
  exact ratLt_not_ratLe_reverse
    BEDC.Real.RatNumLogEnclosure.ratOne_pos oneLeZero

end BEDC.Derived.RHRoute.JensenTuranDegree2
