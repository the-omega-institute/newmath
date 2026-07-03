import BEDC.Derived.RHRoute.ExclusionCertifiedBudget

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.StripExclusionAssembly

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNum

abbrev natRat (n : Nat) : Rat :=
  BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat n

private theorem natRat_apart0_of_pos {n : Nat} (h : 0 < n) :
    ratApart0 (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos h

def q (num den : Nat) (hden : 0 < den) : Rat :=
  ratDivApart (natRat num) (natRat den) (natRat_apart0_of_pos hden)

-- Common-denominator representatives keep kernel reductions small while preserving
-- the intended rational values: 52/40 = 13/10, 20/40 = 1/2, 50/40 = 5/4.
def sigma : Rat :=
  q 52 40 (by decide)

def half : Rat :=
  q 20 40 (by decide)

def sigmaMinusHalf : Rat :=
  ratSub sigma half

def a : Rat :=
  sigmaMinusHalf

def fourFifths : Rat :=
  q 32 40 (by decide)

def fiveFourths : Rat :=
  q 50 40 (by decide)

def A_hi : Rat :=
  q 21263 40000 (by decide)

def P_hi : Rat :=
  ratNeg (q 12628 40000 (by decide))

def E_hi : Rat :=
  q 8452 40000 (by decide)

def K29_lo : Rat :=
  q 6680 40000 (by decide)

def budget : Rat :=
  q 10407 40000 (by decide)

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem ratEq_of_leBool_true_true (x y : Rat)
    (hxy : ratLeBool x y = true) (hyx : ratLeBool y x = true) :
    RatEq x y :=
  ratLe_antisymm (ratLeBool_true_to_ratLe hxy)
    (ratLeBool_true_to_ratLe hyx)

private theorem natRat_nonneg (n : Nat) :
    ratLe ratZero (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumKernel.ratNat_nonneg n

private theorem natRat_pos_of_pos {n : Nat} (h : 0 < n) :
    ratLt ratZero (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos h

private theorem natRat_lt_of_nat_lt {m n : Nat} (h : m < n) :
    ratLt (natRat m) (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_lt_of_nat_lt h

private theorem natRat_le_of_nat_le {m n : Nat} (h : m ≤ n) :
    ratLe (natRat m) (natRat n) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumKernel.ratNat_le_of_nat_le h

private theorem natRat_add (m n : Nat) :
    RatEq (ratAdd (natRat m) (natRat n)) (natRat (m + n)) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_add m n

private theorem natRat_mul (m n : Nat) :
    RatEq (ratMul (natRat m) (natRat n)) (natRat (m * n)) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_mul m n

private theorem natRat_sub_of_le {a b : Nat} (h : b ≤ a) :
    RatEq (ratSub (natRat a) (natRat b)) (natRat (a - b)) := by
  unfold natRat BEDC.Derived.RHRoute.ExclusionCertifiedBudget.natRat
    BEDC.Derived.RHRoute.ThreeFourOneSOS.natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_sub_of_le h

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

private theorem ratLe_lt_trans_local {x y z : Rat} :
    ratLe x y -> ratLt y z -> ratLt x z :=
  BEDC.Derived.RationalUp.ratLe_lt_trans

private theorem ratLt_of_le_of_lt {x y z : Rat} :
    ratLe x y -> ratLt y z -> ratLt x z :=
  ratLe_lt_trans_local

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro xPos yPos
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left yPos xPos
  exact ratLt_respects_local (ratMul_zero_right_local x) (RatEq_refl _) raw

private theorem ratMul_lt_cancel_right_local {a b c : Rat}
    (hc : ratLt ratZero c)
    (h : ratLt (ratMul a c) (ratMul b c)) :
    ratLt a b := by
  apply ratLe_not_le_to_ratLt
  · exact ratMul_le_cancel_right hc (ratLt_to_ratLe h)
  · intro ba
    have reverse :
        ratLe (ratMul b c) (ratMul a c) :=
      ratMul_le_mul_right ba (ratLt_to_ratLe hc)
    exact ratLt_not_ratLe_reverse h reverse

private theorem ratAdd_right_neg_cancel (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratSub_add_cancel_right (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratLe_add_right_cancel {x x' y : Rat} :
    ratLe (ratAdd x y) (ratAdd x' y) -> ratLe x x' := by
  intro h
  have shifted :
      ratLe (ratAdd (ratAdd x y) (ratNeg y))
        (ratAdd (ratAdd x' y) (ratNeg y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratAdd x y) (x' := ratAdd x' y) (y := ratNeg y) h
  exact ratLe_respects
    (ratAdd_right_neg_cancel x y)
    (ratAdd_right_neg_cancel x' y)
    shifted

private theorem ratLt_add_right_mono {x x' y : Rat} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := x) (x' := x') (y := y) (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h (ratLe_add_right_cancel reverse)

private theorem ratSub_eq_of_add_right_eq {x y z : Rat} :
    RatEq (ratAdd x y) z -> RatEq (ratSub z y) x := by
  intro h
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_symm h) (RatEq_refl (ratNeg y)))
    (ratAdd_right_neg_cancel x y)

private theorem ratLe_add_right_of_eq {x y z : Rat} :
    RatEq (ratAdd x y) z -> ratLe (ratSub z y) x := by
  intro h
  exact ratLe_of_RatEq (ratSub_eq_of_add_right_eq h)

private theorem ratLe_neg_anti_local {a b : Rat} :
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

private theorem ratLe_sub_right_of_add_le {x y z : Rat} :
    ratLe (ratAdd x y) z -> ratLe x (ratSub z y) := by
  intro h
  have shifted :
      ratLe (ratAdd (ratAdd x y) (ratNeg y))
        (ratAdd z (ratNeg y)) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := ratAdd x y) (x' := z) (y := ratNeg y) h
  exact ratLe_respects
    (ratAdd_right_neg_cancel x y)
    (RatEq_refl (ratSub z y))
    shifted

private theorem ratSub_le_sub_of_le_of_le {a b c d : Rat} :
    ratLe a b -> ratLe c d -> ratLe (ratSub a d) (ratSub b c) := by
  intro hab hcd
  have negdc : ratLe (ratNeg d) (ratNeg c) := by
    exact ratLe_neg_anti_local hcd
  exact BEDC.Derived.LocatedReal.ratLe_add_mono hab negdc

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

private theorem ratDivApart_lt_same_pos_num_den_strictAnti
    {x a b : Rat}
    (hx : ratLt ratZero x)
    (ha : ratLt ratZero a)
    (hb : ratLt ratZero b)
    (haApart : ratApart0 a)
    (hbApart : ratApart0 b)
    (hab : ratLt a b) :
    ratLt (ratDivApart x b hbApart) (ratDivApart x a haApart) := by
  have leftCancel :
      RatEq (ratMul (ratDivApart x b hbApart) b) x :=
    ratDivApart_mul_cancel_right hbApart
  have rightCancel :
      RatEq (ratMul (ratDivApart x a haApart) a) x :=
    ratDivApart_mul_cancel_right haApart
  have divBPos :
      ratLt ratZero (ratDivApart x b hbApart) := by
    unfold ratDivApart
    exact ratMul_pos_local hx (ratInvApart_pos_of_pos_local hb hbApart)
  have step :
      ratLt (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x b hbApart) b) := by
    exact ratMul_lt_mul_left hab divBPos
  have toX :
      ratLt (ratMul (ratDivApart x b hbApart) a) x :=
    ratLt_of_RatEq_right step leftCancel
  have targetMul :
      ratLt (ratMul (ratDivApart x b hbApart) a)
        (ratMul (ratDivApart x a haApart) a) :=
    ratLt_of_RatEq_right toX (RatEq_symm rightCancel)
  exact ratMul_lt_cancel_right_local ha targetMul

private theorem ratInvApart_respects {x y : Rat}
    (hx : ratApart0 x) (hy : ratApart0 y) (hxy : RatEq x y) :
    RatEq (ratInvApart x hx) (ratInvApart y hy) := by
  have invXx : RatEq (ratMul (ratInvApart x hx) x) ratOne :=
    RatEq_trans _ _ _ (ratMul_comm (ratInvApart x hx) x)
      (ratInvApart_mul x hx)
  have yInvY : RatEq (ratMul y (ratInvApart y hy)) ratOne :=
    ratInvApart_mul y hy
  exact RatEq_trans _ _ _
    (RatEq_symm (ratMul_one_right (ratInvApart x hx)))
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (ratInvApart x hx)) (RatEq_symm yInvY))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratInvApart x hx))
          (ratMul_respects (RatEq_symm hxy)
            (RatEq_refl (ratInvApart y hy))))
        (RatEq_trans _ _ _
          (RatEq_symm (ratMul_assoc (ratInvApart x hx) x
            (ratInvApart y hy)))
          (RatEq_trans _ _ _
            (ratMul_respects invXx (RatEq_refl (ratInvApart y hy)))
            (ratOne_mul_left (ratInvApart y hy))))))

private theorem ratDivApart_respects {A A' D D' : Rat}
    (hD : ratApart0 D) (hD' : ratApart0 D')
    (hA : RatEq A A') (hDeq : RatEq D D') :
    RatEq (ratDivApart A D hD) (ratDivApart A' D' hD') := by
  unfold ratDivApart
  exact ratMul_respects hA (ratInvApart_respects hD hD' hDeq)

private theorem ratDivApart_add_same {A C D : Rat} (hD : ratApart0 D) :
    RatEq (ratAdd (ratDivApart A D hD) (ratDivApart C D hD))
      (ratDivApart (ratAdd A C) D hD) := by
  unfold ratDivApart
  exact RatEq_symm (ratMul_add_right A C (ratInvApart D hD))

private theorem ratDivApart_mul {A D1 C D2 : Rat}
    (h1 : ratApart0 D1) (h2 : ratApart0 D2)
    (h12 : ratApart0 (ratMul D1 D2)) :
    RatEq (ratMul (ratDivApart A D1 h1) (ratDivApart C D2 h2))
      (ratDivApart (ratMul A C) (ratMul D1 D2) h12) := by
  unfold ratDivApart
  have invProduct :
      RatEq (ratInvApart (ratMul D1 D2) h12)
        (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)) :=
    ratInvApart_mul_product h1 h2 h12
  have regroup :
      RatEq
        (ratMul (ratMul A (ratInvApart D1 h1))
          (ratMul C (ratInvApart D2 h2)))
        (ratMul (ratMul A C)
          (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2))) := by
    exact RatEq_trans _ _ _
      (ratMul_assoc A (ratInvApart D1 h1)
        (ratMul C (ratInvApart D2 h2)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl A)
          (RatEq_trans _ _ _
            (RatEq_symm (ratMul_assoc (ratInvApart D1 h1) C
              (ratInvApart D2 h2)))
            (RatEq_trans _ _ _
              (ratMul_respects (ratMul_comm (ratInvApart D1 h1) C)
                (RatEq_refl (ratInvApart D2 h2)))
              (ratMul_assoc C (ratInvApart D1 h1)
                (ratInvApart D2 h2)))))
        (RatEq_symm (ratMul_assoc A C
          (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)))))
  exact RatEq_trans _ _ _ regroup
    (ratMul_respects (RatEq_refl (ratMul A C)) (RatEq_symm invProduct))

private theorem q_add_same_den {a c m : Nat} (hm : 0 < m) :
    RatEq (ratAdd (q a m hm) (q c m hm)) (q (a + c) m hm) := by
  unfold q
  exact RatEq_trans _ _ _
    (ratDivApart_add_same (natRat_apart0_of_pos hm))
    (ratDivApart_respects (natRat_apart0_of_pos hm)
      (natRat_apart0_of_pos hm) (natRat_add a c) (RatEq_refl (natRat m)))

private theorem q_sub_same_den_of_sum {a b diff m : Nat}
    (hm : 0 < m) (hsum : diff + b = a) :
    RatEq (ratSub (q a m hm) (q b m hm)) (q diff m hm) := by
  have addBack :
      RatEq (ratAdd (q diff m hm) (q b m hm)) (q a m hm) := by
    have folded :
        RatEq (ratAdd (q diff m hm) (q b m hm))
          (q (diff + b) m hm) :=
      q_add_same_den hm
    cases hsum
    exact folded
  exact ratSub_eq_of_add_right_eq addBack

private theorem q_mul {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) :
    RatEq (ratMul (q a b hb) (q c d hd)) (q (a * c) (b * d) (Nat.mul_pos hb hd)) := by
  have h12 : ratApart0 (ratMul (natRat b) (natRat d)) :=
    ratMul_apart0 (natRat_apart0_of_pos hb) (natRat_apart0_of_pos hd)
  exact RatEq_trans _ _ _
    (ratDivApart_mul (natRat_apart0_of_pos hb) (natRat_apart0_of_pos hd) h12)
    (RatEq_trans _ _ _
      (ratDivApart_respects h12
        (natRat_apart0_of_pos (Nat.mul_pos hb hd))
        (natRat_mul a c) (natRat_mul b d))
      (RatEq_refl _))

private theorem q_self_eq_one {n : Nat} (hn : 0 < n) :
    RatEq (q n n hn) ratOne := by
  unfold q ratDivApart
  exact ratInvApart_mul (natRat n) (natRat_apart0_of_pos hn)

private theorem ratLe_congr {x x' y y' : Rat}
    (hx : RatEq x x') (hy : RatEq y y') (h : ratLe x' y') : ratLe x y :=
  ratLe_of_RatEq_right (ratLe_of_RatEq_left hx h) (RatEq_symm hy)

private theorem ratNat_mul_le_of_nat_mul_le {a d2 b d1 : Nat}
    (h : a * d2 ≤ b * d1) :
    ratLe (ratMul (natRat a) (natRat d2))
      (ratMul (natRat b) (natRat d1)) :=
  ratLe_congr (natRat_mul a d2) (natRat_mul b d1) (natRat_le_of_nat_le h)

private theorem ratNat_mul_lt_of_nat_mul_lt {a d2 b d1 : Nat}
    (h : a * d2 < b * d1) :
    ratLt (ratMul (natRat a) (natRat d2))
      (ratMul (natRat b) (natRat d1)) :=
  ratLt_respects_local (RatEq_symm (natRat_mul a d2))
    (RatEq_symm (natRat_mul b d1))
    (natRat_lt_of_nat_lt h)

private theorem ratNatMul_pos {d1 d2 : Nat} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ratLt ratZero (ratMul (natRat d1) (natRat d2)) :=
  ratLt_of_RatEq_right (natRat_pos_of_pos (Nat.mul_pos hd1 hd2))
    (RatEq_symm (natRat_mul d1 d2))

private theorem ratDivApart_mul_cancel_pair_right {x d e : Rat}
    (hd : ratApart0 d) :
    RatEq (ratMul (ratDivApart x d hd) (ratMul d e)) (ratMul x e) :=
  RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc (ratDivApart x d hd) d e))
    (ratMul_respects_left (ratDivApart_mul_cancel_right hd))

private theorem ratDivApart_mul_cancel_pair_cross_right {x d e : Rat}
    (he : ratApart0 e) :
    RatEq (ratMul (ratDivApart x e he) (ratMul d e)) (ratMul x d) :=
  RatEq_trans _ _ _
    (ratMul_respects_right (ratMul_comm d e))
    (ratDivApart_mul_cancel_pair_right (x := x) (d := e) (e := d) he)

private theorem ratDivApart_crossLt_rat {A B D1 D2 : Rat}
    (hD1 : ratApart0 D1) (hD2 : ratApart0 D2)
    (hCpos : ratLt ratZero (ratMul D1 D2))
    (hCross : ratLt (ratMul A D2) (ratMul B D1)) :
    ratLt (ratDivApart A D1 hD1) (ratDivApart B D2 hD2) := by
  have hLeftEq :
      RatEq (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2)) (ratMul A D2) :=
    ratDivApart_mul_cancel_pair_right (x := A) (d := D1) (e := D2) hD1
  have hRightEq :
      RatEq (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) (ratMul B D1) :=
    ratDivApart_mul_cancel_pair_cross_right (x := B) (d := D1) (e := D2) hD2
  have hScaled :
      ratLt (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2))
        (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) :=
    ratLt_respects_local (RatEq_symm hLeftEq) (RatEq_symm hRightEq) hCross
  exact ratMul_lt_cancel_right_local hCpos hScaled

private theorem q_crossLt {a d1 b d2 : Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (h : a * d2 < b * d1) :
    ratLt (q a d1 hd1) (q b d2 hd2) := by
  exact ratDivApart_crossLt_rat
    (natRat_apart0_of_pos hd1) (natRat_apart0_of_pos hd2)
    (ratNatMul_pos hd1 hd2)
    (ratNat_mul_lt_of_nat_mul_lt h)

theorem budget_eq :
    RatEq (ratSub (ratAdd (ratAdd A_hi P_hi) E_hi) K29_lo) budget :=
by
  unfold A_hi P_hi E_hi K29_lo budget
  have h1 :
      RatEq (ratAdd (q 21263 40000 (by decide))
          (ratNeg (q 12628 40000 (by decide))))
        (q 8635 40000 (by decide)) := by
    change RatEq
      (ratSub (q 21263 40000 (by decide)) (q 12628 40000 (by decide)))
      (q 8635 40000 (by decide))
    exact q_sub_same_den_of_sum (by decide) rfl
  have h2 :
      RatEq
        (ratAdd
          (ratAdd (q 21263 40000 (by decide))
            (ratNeg (q 12628 40000 (by decide))))
          (q 8452 40000 (by decide)))
        (q 17087 40000 (by decide)) :=
    RatEq_trans _ _ _
      (ratAdd_respects h1 (RatEq_refl (q 8452 40000 (by decide))))
      (q_add_same_den (by decide))
  have h3 :
      RatEq
        (ratSub
          (ratAdd
            (ratAdd (q 21263 40000 (by decide))
              (ratNeg (q 12628 40000 (by decide))))
            (q 8452 40000 (by decide)))
          (q 6680 40000 (by decide)))
        (q 10407 40000 (by decide)) := by
    exact RatEq_trans _ _ _
      (ratAdd_respects h2 (RatEq_refl (ratNeg (q 6680 40000 (by decide)))))
      (q_sub_same_den_of_sum (by decide) rfl)
  exact h3

theorem budget_lt_fiveFourths :
    ratLt budget fiveFourths :=
by
  unfold budget fiveFourths
  exact q_crossLt (by decide) (by decide) (by decide)

theorem sigma_minus_half_eq_fourFifths :
    RatEq sigmaMinusHalf fourFifths :=
by
  unfold sigmaMinusHalf sigma half fourFifths
  exact q_sub_same_den_of_sum (by decide) rfl

theorem fourFifths_pos :
    ratLt ratZero fourFifths :=
by
  unfold fourFifths q ratDivApart
  exact ratMul_pos_local (natRat_pos_of_pos (by decide))
    (ratInvApart_pos_of_pos_local
      (natRat_pos_of_pos (by decide))
      (natRat_apart0_of_pos (by decide)))

theorem fiveFourths_eq_inv_fourFifths :
    RatEq fiveFourths (ratInvApart fourFifths (ratApart0_of_pos fourFifths_pos)) :=
by
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (c := fourFifths)
  · exact ratApart0_of_pos fourFifths_pos
  · have leftOne :
        RatEq (ratMul fiveFourths fourFifths) ratOne := by
      unfold fiveFourths fourFifths
      exact RatEq_trans _ _ _
        (q_mul (by decide) (by decide))
        (q_self_eq_one (by decide))
    have rightOne :
        RatEq
          (ratMul (ratInvApart fourFifths (ratApart0_of_pos fourFifths_pos))
            fourFifths)
          ratOne :=
      RatEq_trans _ _ _
        (ratMul_comm (ratInvApart fourFifths (ratApart0_of_pos fourFifths_pos))
          fourFifths)
        (ratInvApart_mul fourFifths (ratApart0_of_pos fourFifths_pos))
    exact RatEq_trans _ _ _ leftOne (RatEq_symm rightOne)

private theorem sigma_sub_beta_pos {beta : Rat}
    (hhi : ratLt beta sigma) :
    ratLt ratZero (ratSub sigma beta) :=
  sub_pos_of_lt hhi

theorem sigma_sub_beta_lt_fourFifths (beta : Rat)
    (hlo : ratLt half beta) :
    ratLt (ratSub sigma beta) fourFifths := by
  have raw : ratLt (ratSub sigma beta) (ratSub sigma half) :=
    const_sub_strictAnti hlo
  exact ratLt_of_RatEq_right raw sigma_minus_half_eq_fourFifths

theorem offline_self_gt (beta : Rat)
    (hlo : ratLt half beta) (hhi : ratLt beta sigma) :
    ratLt fiveFourths
      (ratInvApart (ratSub sigma beta)
        (ratApart0_of_pos (sigma_sub_beta_pos hhi))) := by
  have denPos : ratLt ratZero (ratSub sigma beta) :=
    sigma_sub_beta_pos hhi
  have denLt : ratLt (ratSub sigma beta) fourFifths :=
    sigma_sub_beta_lt_fourFifths beta hlo
  have invStrict :
      ratLt
        (ratDivApart ratOne fourFifths
          (ratApart0_of_pos fourFifths_pos))
        (ratDivApart ratOne (ratSub sigma beta)
          (ratApart0_of_pos denPos)) :=
    ratDivApart_lt_same_pos_num_den_strictAnti
      BEDC.Real.RatNumLogEnclosure.ratOne_pos denPos fourFifths_pos
      (ratApart0_of_pos denPos) (ratApart0_of_pos fourFifths_pos)
      denLt
  have leftEq :
      RatEq fiveFourths
        (ratDivApart ratOne fourFifths
          (ratApart0_of_pos fourFifths_pos)) := by
    unfold ratDivApart
    exact RatEq_trans _ _ _
      fiveFourths_eq_inv_fourFifths
      (RatEq_symm
        (ratOne_mul_left
          (ratInvApart fourFifths (ratApart0_of_pos fourFifths_pos))))
  have rightEq :
      RatEq
        (ratDivApart ratOne (ratSub sigma beta)
          (ratApart0_of_pos denPos))
        (ratInvApart (ratSub sigma beta)
          (ratApart0_of_pos denPos)) := by
    unfold ratDivApart
    exact ratOne_mul_left _
  exact ratLt_respects_local (RatEq_symm leftEq) rightEq invStrict

private theorem ratAdd_le_add3 {a b c A B C : Rat}
    (ha : ratLe a A) (hb : ratLe b B) (hc : ratLe c C) :
    ratLe (ratAdd (ratAdd a b) c) (ratAdd (ratAdd A B) C) :=
  ratAdd_le_add (ratAdd_le_add ha hb) hc

theorem Kunk_cap_of_bounds (sumK K29 Kunk A P E : Rat)
    (hid : RatEq sumK (ratAdd (ratAdd A P) E))
    (hsplit : RatEq sumK (ratAdd K29 Kunk))
    (hA : ratLe A A_hi) (hP : ratLe P P_hi) (hE : ratLe E E_hi)
    (hK29 : ratLe K29_lo K29) :
    ratLe Kunk budget := by
  have splitLe :
      ratLe (ratAdd K29 Kunk) (ratAdd (ratAdd A P) E) :=
    ratLe_respects hsplit hid (ratLe_refl sumK)
  have splitLeComm :
      ratLe (ratAdd Kunk K29) (ratAdd (ratAdd A P) E) :=
    ratLe_of_RatEq_left (ratAdd_comm Kunk K29) splitLe
  have unkLeExpr :
      ratLe Kunk (ratSub (ratAdd (ratAdd A P) E) K29) :=
    ratLe_sub_right_of_add_le splitLeComm
  have exprLeCert :
      ratLe (ratSub (ratAdd (ratAdd A P) E) K29)
        (ratSub (ratAdd (ratAdd A_hi P_hi) E_hi) K29_lo) :=
    ratSub_le_sub_of_le_of_le
      (ratAdd_le_add3 hA hP hE) hK29
  have certLeBudget :
      ratLe (ratSub (ratAdd (ratAdd A_hi P_hi) E_hi) K29_lo) budget :=
    ratLe_of_RatEq budget_eq
  exact ratLe_trans unkLeExpr (ratLe_trans exprLeCert certLeBudget)

theorem strip_exclusion_of_certificates (_sumK Kunk selfK : Rat)
    (hdecomp : ratLe selfK Kunk)
    (hcap : ratLe Kunk budget)
    (hself : ratLt fiveFourths selfK) :
    False := by
  have cert : ratLe fiveFourths Kunk :=
    ratLe_trans (ratLt_to_ratLe hself) hdecomp
  exact BEDC.Derived.RHRoute.ExclusionCertifiedBudget.budget_exceeded_absurd
    fiveFourths Kunk budget cert hcap budget_lt_fiveFourths

-- Analytic content is carried as data: the explicit-formula identity, the zero
-- split, and the four certified rational bounds are hypotheses. The theorems
-- here assemble only rational arithmetic, reciprocal monotonicity, and the
-- contradiction for the window [17,18]; they do not assert RH or any global
-- critical-strip statement.
structure StripExclusionData where
  sumK : Rat
  K29 : Rat
  Kunk : Rat
  A : Rat
  P : Rat
  E : Rat
  explicit_formula_at_zero_height :
    RatEq sumK (ratAdd (ratAdd A P) E)
  zero_split_at_zero_height :
    RatEq sumK (ratAdd K29 Kunk)
  archimedean_bound : ratLe A A_hi
  prime_bound : ratLe P P_hi
  tail_bound : ratLe E E_hi
  first_zeros_bound : ratLe K29_lo K29
  unknown_block_nonneg : ratLe ratZero Kunk

theorem no_offline_zero_17_18 (data : StripExclusionData)
    (beta selfK : Rat)
    (hbeta : ratLt half beta)
    (hupper : ratLt beta sigma)
    (hself :
      RatEq selfK
        (ratInvApart (ratSub sigma beta)
          (ratApart0_of_pos (sigma_sub_beta_pos hupper))))
    (hunknown : ratLe selfK data.Kunk) :
    False := by
  have cap : ratLe data.Kunk budget :=
    Kunk_cap_of_bounds data.sumK data.K29 data.Kunk data.A data.P data.E
      data.explicit_formula_at_zero_height
      data.zero_split_at_zero_height
      data.archimedean_bound data.prime_bound data.tail_bound
      data.first_zeros_bound
  have selfGtRaw :
      ratLt fiveFourths
        (ratInvApart (ratSub sigma beta)
          (ratApart0_of_pos (sigma_sub_beta_pos hupper))) :=
    offline_self_gt beta hbeta hupper
  have selfGt : ratLt fiveFourths selfK :=
    ratLt_of_RatEq_right selfGtRaw (RatEq_symm hself)
  exact strip_exclusion_of_certificates data.sumK data.Kunk selfK
    hunknown cap selfGt

end BEDC.Derived.RHRoute.StripExclusionAssembly
