import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumTrig

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  RatNumKernel.Rat

def ratFour : Rat :=
  ratNat 4

def ratEight : Rat :=
  ratNat 8

def ratSixteen : Rat :=
  ratNat 16

def ratThirtyTwo : Rat :=
  ratNat 32

def ratForty : Rat :=
  ratNat 40

private theorem intLt_nat_of_lt (m n : Nat) (h : m < n) :
    intLtUp
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n)) := by
  unfold intLtUp BEDC.Derived.IntUp.intLt intOfNat intToPair
  rw [BEDC.Derived.IntUp.natToUnary_length]
  rw [BEDC.Derived.IntUp.natToUnary_length]
  rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left]
  rw [Nat.add_zero]
  exact h

theorem ratNat_pos_of_pos {n : Nat} (h : 0 < n) :
    ratLt ratZero (ratNat n) := by
  unfold ratLt ratZero ratNat intToRat ratDenInt
  change intLtUp
    (IntMul intZero (intOfNat NatOne (unary_e1_closed unary_empty)))
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
  have leftZero :
      IntEq
        (IntMul intZero (intOfNat NatOne (unary_e1_closed unary_empty)))
        intZero :=
    intMul_zero_left (intOfNat NatOne (unary_e1_closed unary_empty))
  have rightId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
  exact intLt_respects (IntEq_symm leftZero) (IntEq_symm rightId)
    (intLt_nat_of_lt 0 n h)

theorem ratNat_lt_of_nat_lt {m n : Nat} (h : m < n) :
    ratLt (ratNat m) (ratNat n) := by
  unfold ratLt ratNat ratDenInt
  change intLtUp
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
    (IntMul
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
      (intOfNat NatOne (unary_e1_closed unary_empty)))
  have leftId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary m)
            (BEDC.Derived.IntUp.natToUnary_unary m))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary m)
          (BEDC.Derived.IntUp.natToUnary_unary m)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary m)
        (BEDC.Derived.IntUp.natToUnary_unary m))
  have rightId :
      IntEq
        (IntMul
          (intOfNat (BEDC.Derived.IntUp.natToUnary n)
            (BEDC.Derived.IntUp.natToUnary_unary n))
          (intOfNat NatOne (unary_e1_closed unary_empty)))
        (intOfNat (BEDC.Derived.IntUp.natToUnary n)
          (BEDC.Derived.IntUp.natToUnary_unary n)) :=
    intMul_one_right
      (intOfNat (BEDC.Derived.IntUp.natToUnary n)
        (BEDC.Derived.IntUp.natToUnary_unary n))
  exact intLt_respects (IntEq_symm leftId) (IntEq_symm rightId)
    (intLt_nat_of_lt m n h)

theorem ratNat_apart0_of_pos {n : Nat} (h : 0 < n) :
    ratApart0 (ratNat n) :=
  ratApart0_of_pos (ratNat_pos_of_pos h)

def qNat (a b : Nat) (hb : 0 < b) : Rat :=
  ratDivApart (ratNat a) (ratNat b)
    (ratNat_apart0_of_pos hb)

def qOneFive : Rat :=
  qNat 1 5 (by decide)

def qOneTwoThirtyNine : Rat :=
  qNat 1 239 (by decide)

theorem qNat_nonneg (a b : Nat) (hb : 0 < b) :
    ratLe ratZero (qNat a b hb) := by
  unfold qNat
  exact ratDivApart_nonneg_of_nonneg_pos
    (ratNat_nonneg a)
    (ratNat_pos_of_pos hb)
    (ratNat_apart0_of_pos hb)

theorem qNat_lt_one_of_num_lt_den {a b : Nat}
    (hb : 0 < b)
    (hab : a < b) :
    ratLt (qNat a b hb) ratOne := by
  unfold qNat
  let q := ratDivApart (ratNat a) (ratNat b)
    (ratNat_apart0_of_pos hb)
  have hden_pos : ratLt ratZero (ratNat b) :=
    ratNat_pos_of_pos hb
  have hcancel :
      RatEq
        (ratMul q (ratNat b))
        (ratNat a) :=
    ratDivApart_mul_cancel_right
      (ratNat_apart0_of_pos hb)
  have hnum_lt_den : ratLt (ratNat a) (ratNat b) :=
    ratNat_lt_of_nat_lt hab
  apply ratLe_not_le_to_ratLt
  · have productLe :
        ratLe
          (ratMul q (ratNat b))
          (ratMul ratOne (ratNat b)) :=
      ratLe_of_RatEq_left hcancel
        (ratLe_of_RatEq_right
          (ratLt_to_ratLe hnum_lt_den)
          (RatEq_symm (ratOne_mul_left (ratNat b))))
    exact ratMul_le_cancel_right hden_pos productLe
  · intro oneLeQ
    have prodLe :
        ratLe
          (ratMul ratOne (ratNat b))
          (ratMul q (ratNat b)) :=
      ratMul_le_mul_right oneLeQ (ratLt_to_ratLe hden_pos)
    have denLeNum :
        ratLe (ratNat b) (ratNat a) :=
      ratLe_of_RatEq_left (RatEq_symm (ratOne_mul_left (ratNat b)))
        (ratLe_of_RatEq_right prodLe hcancel)
    exact ratLt_not_ratLe_reverse hnum_lt_den denLeNum

theorem qOneFive_nonneg :
    ratLe ratZero qOneFive :=
  qNat_nonneg 1 5 (by decide)

theorem qOneFive_lt_one :
    ratLt qOneFive ratOne :=
  qNat_lt_one_of_num_lt_den (by decide) (by decide)

theorem qOneTwoThirtyNine_nonneg :
    ratLe ratZero qOneTwoThirtyNine :=
  qNat_nonneg 1 239 (by decide)

theorem qOneTwoThirtyNine_lt_one :
    ratLt qOneTwoThirtyNine ratOne :=
  qNat_lt_one_of_num_lt_den (by decide) (by decide)

theorem ratLe_neg_anti {a b : Rat} :
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

theorem ratNeg_nonpos_of_nonneg {a : Rat} :
    ratLe ratZero a -> ratLe (ratNeg a) ratZero := by
  intro ha
  have raw : ratLe (ratAdd ratZero (ratNeg a)) ratZero :=
    ratSub_le_left_of_nonneg (x := ratZero) (y := a) ha
  exact ratLe_of_RatEq_left (RatEq_symm (ratZero_add_left (ratNeg a))) raw

theorem ratNeg_le_self_of_nonneg {a : Rat} :
    ratLe ratZero a -> ratLe (ratNeg a) a := by
  intro ha
  exact ratLe_trans (ratNeg_nonpos_of_nonneg ha) ha

theorem ratNeg_zero :
    RatEq (ratNeg ratZero) ratZero := by
  have h : RatEq (ratAdd (ratNeg ratZero) ratZero) ratZero :=
    BEDC.Derived.LocatedReal.ratNeg_add_local ratZero
  exact RatEq_trans _ _ _
    (RatEq_symm (ratAdd_zero_right (ratNeg ratZero)))
    h

def signedOddTerm (x : Rat) (k : Nat) : Rat :=
  if k % 2 = 0 then oddTerm x k else ratNeg (oddTerm x k)

def arctanTerm (x : Rat) (k : Nat) : Rat :=
  signedOddTerm x k

def arctanPart (x : Rat) (M : Nat) : Rat :=
  ratSum M (arctanTerm x)

def arctanTailSigned (x : Rat) (M K : Nat) : Rat :=
  ratSum K (fun j => arctanTerm x (M + j))

def arctanTailBound
    (x : Rat)
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne)
    (M : Nat) : Rat :=
  oddTailBound x hx0 hx1 M

def arctanLo
    (x : Rat)
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne)
    (M : Nat) : Rat :=
  ratSub (arctanPart x M) (arctanTailBound x hx0 hx1 M)

def arctanHi
    (x : Rat)
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne)
    (M : Nat) : Rat :=
  ratAdd (arctanPart x M) (arctanTailBound x hx0 hx1 M)

def SeriesEnclosedFrom
    (term : Nat -> Rat)
    (M : Nat)
    (lo hi : Rat) : Prop :=
  ∀ K : Nat, ratLe lo (ratSum (M + K) term) ∧
    ratLe (ratSum (M + K) term) hi

theorem signedOddTerm_upper
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (k : Nat) :
    ratLe (signedOddTerm x k) (oddTerm x k) := by
  unfold signedOddTerm
  by_cases h : k % 2 = 0
  · rw [if_pos h]
    exact ratLe_refl (oddTerm x k)
  · rw [if_neg h]
    exact ratNeg_le_self_of_nonneg (oddTerm_nonneg hx0 k)

theorem signedOddTerm_lower
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (k : Nat) :
    ratLe (ratNeg (oddTerm x k)) (signedOddTerm x k) := by
  unfold signedOddTerm
  by_cases h : k % 2 = 0
  · rw [if_pos h]
    exact ratNeg_le_self_of_nonneg (oddTerm_nonneg hx0 k)
  · rw [if_neg h]
    exact ratLe_refl (ratNeg (oddTerm x k))

theorem ratSum_neg
    (f : Nat -> Rat)
    (K : Nat) :
    RatEq (ratNeg (ratSum K f))
      (ratSum K (fun j => ratNeg (f j))) := by
  induction K with
  | zero =>
      change RatEq (ratNeg ratZero) ratZero
      exact ratNeg_zero
  | succ K ih =>
      change
        RatEq
          (ratNeg (ratAdd (ratSum K f) (f K)))
          (ratAdd (ratSum K (fun j => ratNeg (f j))) (ratNeg (f K)))
      exact RatEq_trans _ _ _
        (BEDC.Derived.LocatedReal.ratNeg_add_dist_local
          (ratSum K f) (f K))
        (ratAdd_respects ih (RatEq_refl (ratNeg (f K))))

theorem arctanTailSigned_upper
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (M K : Nat) :
    ratLe (arctanTailSigned x M K) (oddTail x M K) := by
  unfold arctanTailSigned oddTail arctanTerm
  apply ratSum_le_sum
  intro j _hj
  exact signedOddTerm_upper hx0 (M + j)

theorem arctanTailSigned_lower_sum
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (M K : Nat) :
    ratLe
      (ratSum K (fun j => ratNeg (oddTerm x (M + j))))
      (arctanTailSigned x M K) := by
  unfold arctanTailSigned arctanTerm
  apply ratSum_le_sum
  intro j _hj
  exact signedOddTerm_lower hx0 (M + j)

theorem arctanTailSigned_lower
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne)
    (M K : Nat) :
    ratLe
      (ratNeg (arctanTailBound x hx0 hx1 M))
      (arctanTailSigned x M K) := by
  have htail :
      ratLe (oddTail x M K) (arctanTailBound x hx0 hx1 M) := by
    unfold arctanTailBound
    exact geom_odd_tail_kernel_raw x hx0 hx1 M K
  have hneg :
      ratLe
        (ratNeg (arctanTailBound x hx0 hx1 M))
        (ratNeg (oddTail x M K)) :=
    ratLe_neg_anti htail
  have hsumEq :
      RatEq
        (ratNeg (oddTail x M K))
        (ratSum K (fun j => ratNeg (oddTerm x (M + j)))) := by
    unfold oddTail
    exact ratSum_neg (fun j => oddTerm x (M + j)) K
  have htoSum :
      ratLe
        (ratNeg (arctanTailBound x hx0 hx1 M))
        (ratSum K (fun j => ratNeg (oddTerm x (M + j)))) :=
    ratLe_of_RatEq_right hneg hsumEq
  exact ratLe_trans htoSum (arctanTailSigned_lower_sum hx0 M K)

theorem arctanTailSigned_bound
    {x : Rat}
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne)
    (M K : Nat) :
    ratLe
      (ratNeg (arctanTailBound x hx0 hx1 M))
      (arctanTailSigned x M K) ∧
    ratLe
      (arctanTailSigned x M K)
      (arctanTailBound x hx0 hx1 M) := by
  have upperToOdd :
      ratLe (arctanTailSigned x M K) (oddTail x M K) :=
    arctanTailSigned_upper hx0 M K
  have oddToBound :
      ratLe (oddTail x M K) (arctanTailBound x hx0 hx1 M) := by
    unfold arctanTailBound
    exact geom_odd_tail_kernel_raw x hx0 hx1 M K
  exact And.intro
    (arctanTailSigned_lower hx0 hx1 M K)
    (ratLe_trans upperToOdd oddToBound)

theorem arctanPart_add_tail (x : Rat) (M K : Nat) :
    RatEq (arctanPart x (M + K))
      (ratAdd (arctanPart x M) (arctanTailSigned x M K)) := by
  induction K with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (arctanPart x M)
        (ratAdd (arctanPart x M) ratZero)
      exact RatEq_symm (ratAdd_zero_right (arctanPart x M))
  | succ K ih =>
      rw [Nat.add_succ]
      change RatEq
        (ratAdd (ratSum (M + K) (arctanTerm x))
          (arctanTerm x (M + K)))
        (ratAdd (arctanPart x M)
          (ratAdd (arctanTailSigned x M K)
            (arctanTerm x (M + K))))
      have regroup :
          RatEq
            (ratAdd
              (ratAdd (arctanPart x M) (arctanTailSigned x M K))
              (arctanTerm x (M + K)))
            (ratAdd (arctanPart x M)
              (ratAdd (arctanTailSigned x M K)
                (arctanTerm x (M + K)))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (arctanPart x M)
          (arctanTailSigned x M K)
          (arctanTerm x (M + K))
      exact RatEq_trans _ _ _
        (ratAdd_respects ih (RatEq_refl (arctanTerm x (M + K))))
        regroup

theorem arctan_full_enclosure_rat
    (x : Rat)
    (M : Nat)
    (hx0 : ratLe ratZero x)
    (hx1 : ratLt x ratOne) :
    SeriesEnclosedFrom
      (arctanTerm x)
      M
      (arctanLo x hx0 hx1 M)
      (arctanHi x hx0 hx1 M) := by
  intro K
  have hsplit :
      RatEq (arctanPart x (M + K))
        (ratAdd (arctanPart x M) (arctanTailSigned x M K)) :=
    arctanPart_add_tail x M K
  have htail :=
    arctanTailSigned_bound hx0 hx1 M K
  have hlo :
      ratLe
        (arctanLo x hx0 hx1 M)
        (ratAdd (arctanPart x M) (arctanTailSigned x M K)) := by
    unfold arctanLo ratSub
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (arctanPart x M))
      htail.left
  have hhi :
      ratLe
        (ratAdd (arctanPart x M) (arctanTailSigned x M K))
        (arctanHi x hx0 hx1 M) := by
    unfold arctanHi
    exact BEDC.Derived.LocatedReal.ratLe_add_mono
      (ratLe_refl (arctanPart x M))
      htail.right
  exact And.intro
    (ratLe_of_RatEq_right hlo (RatEq_symm hsplit))
    (ratLe_of_RatEq_left hsplit hhi)

def ATAN_M_PI : Nat :=
  10

def atanOneFiveLo : Rat :=
  arctanLo qOneFive qOneFive_nonneg qOneFive_lt_one ATAN_M_PI

def atanOneFiveHi : Rat :=
  arctanHi qOneFive qOneFive_nonneg qOneFive_lt_one ATAN_M_PI

def atanOneTwoThirtyNineLo : Rat :=
  arctanLo
    qOneTwoThirtyNine
    qOneTwoThirtyNine_nonneg
    qOneTwoThirtyNine_lt_one
    ATAN_M_PI

def atanOneTwoThirtyNineHi : Rat :=
  arctanHi
    qOneTwoThirtyNine
    qOneTwoThirtyNine_nonneg
    qOneTwoThirtyNine_lt_one
    ATAN_M_PI

def piFormalMachinPart (K5 K239 : Nat) : Rat :=
  ratSub
    (ratMul ratSixteen
      (ratSum (ATAN_M_PI + K5) (arctanTerm qOneFive)))
    (ratMul ratFour
      (ratSum (ATAN_M_PI + K239) (arctanTerm qOneTwoThirtyNine)))

def piLo : Rat :=
  ratSub
    (ratMul ratSixteen atanOneFiveLo)
    (ratMul ratFour atanOneTwoThirtyNineHi)

def piHi : Rat :=
  ratSub
    (ratMul ratSixteen atanOneFiveHi)
    (ratMul ratFour atanOneTwoThirtyNineLo)

def piWidth : Rat :=
  ratSub piHi piLo

def PiMachinEnclosedFrom (lo hi : Rat) : Prop :=
  ∀ K5 K239 : Nat, ratLe lo (piFormalMachinPart K5 K239) ∧
    ratLe (piFormalMachinPart K5 K239) hi

theorem piFormal_machin_M10_enclosed :
    PiMachinEnclosedFrom piLo piHi := by
  intro K5 K239
  have h5 :
      SeriesEnclosedFrom
        (arctanTerm qOneFive)
        ATAN_M_PI
        atanOneFiveLo
        atanOneFiveHi := by
    unfold atanOneFiveLo atanOneFiveHi
    exact arctan_full_enclosure_rat
      qOneFive ATAN_M_PI qOneFive_nonneg qOneFive_lt_one
  have h239 :
      SeriesEnclosedFrom
        (arctanTerm qOneTwoThirtyNine)
        ATAN_M_PI
        atanOneTwoThirtyNineLo
        atanOneTwoThirtyNineHi := by
    unfold atanOneTwoThirtyNineLo atanOneTwoThirtyNineHi
    exact arctan_full_enclosure_rat
      qOneTwoThirtyNine
      ATAN_M_PI
      qOneTwoThirtyNine_nonneg
      qOneTwoThirtyNine_lt_one
  let S5 := ratSum (ATAN_M_PI + K5) (arctanTerm qOneFive)
  let S239 :=
    ratSum (ATAN_M_PI + K239) (arctanTerm qOneTwoThirtyNine)
  have h5lo : ratLe atanOneFiveLo S5 :=
    (h5 K5).left
  have h5hi : ratLe S5 atanOneFiveHi :=
    (h5 K5).right
  have h239lo : ratLe atanOneTwoThirtyNineLo S239 :=
    (h239 K239).left
  have h239hi : ratLe S239 atanOneTwoThirtyNineHi :=
    (h239 K239).right
  have h16nonneg : ratLe ratZero ratSixteen := by
    unfold ratSixteen
    exact ratNat_nonneg 16
  have h4nonneg : ratLe ratZero ratFour := by
    unfold ratFour
    exact ratNat_nonneg 4
  have h16lo :
      ratLe
        (ratMul ratSixteen atanOneFiveLo)
        (ratMul ratSixteen S5) :=
    ratMul_le_mul_nonneg_left h5lo h16nonneg
  have h16hi :
      ratLe
        (ratMul ratSixteen S5)
        (ratMul ratSixteen atanOneFiveHi) :=
    ratMul_le_mul_nonneg_left h5hi h16nonneg
  have h4lo :
      ratLe
        (ratMul ratFour atanOneTwoThirtyNineLo)
        (ratMul ratFour S239) :=
    ratMul_le_mul_nonneg_left h239lo h4nonneg
  have h4hi :
      ratLe
        (ratMul ratFour S239)
        (ratMul ratFour atanOneTwoThirtyNineHi) :=
    ratMul_le_mul_nonneg_left h239hi h4nonneg
  have hnegLo :
      ratLe
        (ratNeg (ratMul ratFour atanOneTwoThirtyNineHi))
        (ratNeg (ratMul ratFour S239)) :=
    ratLe_neg_anti h4hi
  have hnegHi :
      ratLe
        (ratNeg (ratMul ratFour S239))
        (ratNeg (ratMul ratFour atanOneTwoThirtyNineLo)) :=
    ratLe_neg_anti h4lo
  have hlo :
      ratLe
        (ratSub (ratMul ratSixteen atanOneFiveLo)
          (ratMul ratFour atanOneTwoThirtyNineHi))
        (ratSub (ratMul ratSixteen S5)
          (ratMul ratFour S239)) := by
    unfold ratSub
    exact BEDC.Derived.LocatedReal.ratLe_add_mono h16lo hnegLo
  have hhi :
      ratLe
        (ratSub (ratMul ratSixteen S5)
          (ratMul ratFour S239))
        (ratSub (ratMul ratSixteen atanOneFiveHi)
          (ratMul ratFour atanOneTwoThirtyNineLo)) := by
    unfold ratSub
    exact BEDC.Derived.LocatedReal.ratLe_add_mono h16hi hnegHi
  unfold piLo piHi piFormalMachinPart
  exact And.intro hlo hhi

structure SinCosTaylorObligation where
  term : Nat -> Rat
  truncation : Nat
  lo : Rat
  hi : Rat
  enclosed : SeriesEnclosedFrom term truncation lo hi

inductive RatNumTrigRealBridgeObligation : Type
  | analyticArctanBridge
  | analyticMachinBridge
  | reducedSinCosTaylorBridge

end BEDC.Real.RatNumTrig
