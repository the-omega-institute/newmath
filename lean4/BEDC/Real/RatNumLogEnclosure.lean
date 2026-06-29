import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

namespace BEDC.Real.RatNumLogEnclosure

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PadicUp

abbrev Rat : Type :=
  RatNumKernel.Rat

def ratThree : Rat :=
  ratNat 3

theorem ratOne_nonneg :
    ratLe ratZero ratOne := by
  apply ratNonneg_of_num
  unfold ratOne intToRat intOne intOfNat
  exact intLe_zero_of_nat NatOne (unary_e1_closed unary_empty)

theorem ratOne_apart :
    ratApart0 ratOne := by
  unfold ratApart0 ratOne intToRat intOne intOfNat
  exact Or.inr (hsame_refl NatOne)

theorem ratOne_pos :
    ratLt ratZero ratOne := by
  apply ratLe_not_le_to_ratLt
  · exact ratOne_nonneg
  · intro oneLeZero
    exact intApart0_not_zero_pair ratOne_apart
      (RatEq_zero_num (ratLe_antisymm oneLeZero ratOne_nonneg))

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

def twice (x : Rat) : Rat :=
  ratMul ratTwo x

def atanhPart (z : Rat) (M : Nat) : Rat :=
  ratSum M (fun j => oddTerm z j)

def atanhFormalSeries (z : Rat) (K : Nat) : Rat :=
  twice (atanhPart z K)

def SeriesEnclosedFrom
    (s : Nat -> Rat)
    (M : Nat)
    (lo hi : Rat) : Prop :=
  ∀ K : Nat, ratLe lo (s (M + K)) ∧ ratLe (s (M + K)) hi

theorem ratSum_nonneg {f : Nat -> Rat}
    (h : ∀ j : Nat, ratLe ratZero (f j)) :
    ∀ K : Nat, ratLe ratZero (ratSum K f)
  | 0 => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | Nat.succ K => by
      change ratLe ratZero (ratAdd (ratSum K f) (f K))
      have left : ratLe (ratAdd ratZero ratZero) (ratAdd (ratSum K f) (f K)) := by
        exact ratAdd_le_add (ratSum_nonneg h K) (h K)
      exact ratLe_of_RatEq_left (ratZero_add_left ratZero) left

theorem ratLe_add_nonneg_right (x y : Rat)
    (hy : ratLe ratZero y) :
    ratLe x (ratAdd x y) := by
  have shifted : ratLe (ratAdd x ratZero) (ratAdd x y) := by
    exact BEDC.Derived.LocatedReal.ratLe_add_left_mono (x := x) hy
  exact ratLe_of_RatEq_left (RatEq_symm (ratAdd_zero_right x)) shifted

theorem ratMul_le_mul_left_nonneg (c a b : Rat)
    (hc : ratLe ratZero c)
    (hab : ratLe a b) :
    ratLe (ratMul c a) (ratMul c b) :=
  ratMul_le_mul_nonneg_left hab hc

theorem atanhPart_add_tail (z : Rat) (M K : Nat) :
    RatEq (atanhPart z (M + K))
      (ratAdd (atanhPart z M) (oddTail z M K)) := by
  induction K with
  | zero =>
      rw [Nat.add_zero]
      change RatEq (atanhPart z M)
        (ratAdd (atanhPart z M) ratZero)
      exact RatEq_symm (ratAdd_zero_right (atanhPart z M))
  | succ K ih =>
      rw [Nat.add_succ]
      change RatEq
        (ratAdd (ratSum (M + K) (fun j => oddTerm z j))
          (oddTerm z (M + K)))
        (ratAdd (atanhPart z M)
          (ratAdd (oddTail z M K) (oddTerm z (M + K))))
      have regroup :
          RatEq
            (ratAdd (ratAdd (atanhPart z M) (oddTail z M K))
              (oddTerm z (M + K)))
            (ratAdd (atanhPart z M)
              (ratAdd (oddTail z M K) (oddTerm z (M + K)))) :=
        BEDC.Derived.LocatedReal.ratAdd_assoc_local
          (atanhPart z M) (oddTail z M K) (oddTerm z (M + K))
      exact RatEq_trans _ _ _
        (ratAdd_respects ih (RatEq_refl (oddTerm z (M + K))))
        regroup

theorem oddTail_nonneg (z : Rat)
    (hz0 : ratLe ratZero z)
    (M K : Nat) :
    ratLe ratZero (oddTail z M K) := by
  unfold oddTail
  apply ratSum_nonneg
  intro j
  exact oddTerm_nonneg hz0 (M + j)

theorem atanh_full_enclosure
    (z : Rat)
    (hz0 : ratLe ratZero z)
    (hz1 : ratLt z ratOne)
    (M : Nat) :
    SeriesEnclosedFrom
      (atanhFormalSeries z)
      M
      (twice (atanhPart z M))
      (twice
        (ratAdd
          (atanhPart z M)
          (atanhTailBound z hz0 hz1 M))) := by
  intro K
  have hsplit :
      RatEq (atanhPart z (M + K))
        (ratAdd (atanhPart z M) (oddTail z M K)) :=
    atanhPart_add_tail z M K
  have htail_nonneg :
      ratLe ratZero (oddTail z M K) :=
    oddTail_nonneg z hz0 M K
  have htail_le_bound :
      ratLe (oddTail z M K) (atanhTailBound z hz0 hz1 M) := by
    change ratLe (oddTail z M K) (oddTailBound z hz0 hz1 M)
    exact atanh_tail_kernel z hz0 hz1 M K
  have hpart_lo :
      ratLe (atanhPart z M) (atanhPart z (M + K)) :=
    ratLe_of_RatEq_right
      (ratLe_add_nonneg_right (atanhPart z M) (oddTail z M K)
        htail_nonneg)
      (RatEq_symm hsplit)
  have hpart_hi :
      ratLe
        (atanhPart z (M + K))
        (ratAdd (atanhPart z M) (atanhTailBound z hz0 hz1 M)) :=
    ratLe_of_RatEq_left hsplit
      (BEDC.Derived.LocatedReal.ratLe_add_left_mono
        (x := atanhPart z M) htail_le_bound)
  have hlo :
      ratLe
        (twice (atanhPart z M))
        (twice (atanhPart z (M + K))) := by
    unfold twice
    exact ratMul_le_mul_left_nonneg ratTwo
      (atanhPart z M)
      (atanhPart z (M + K))
      ratTwo_nonneg
      hpart_lo
  have hhi :
      ratLe
        (twice (atanhPart z (M + K)))
        (twice
          (ratAdd
            (atanhPart z M)
            (atanhTailBound z hz0 hz1 M))) := by
    unfold twice
    exact ratMul_le_mul_left_nonneg ratTwo
      (atanhPart z (M + K))
      (ratAdd (atanhPart z M) (atanhTailBound z hz0 hz1 M))
      ratTwo_nonneg
      hpart_hi
  exact And.intro hlo hhi

def zNum (N : Nat) : Rat :=
  ratNat (N - 1)

def zDen (N : Nat) : Rat :=
  ratNat (N + 1)

theorem zDen_pos (N : Nat) :
    ratLt ratZero (zDen N) := by
  unfold zDen
  exact ratNat_pos_of_pos (Nat.succ_pos N)

theorem zDen_apart0 (N : Nat) :
    ratApart0 (zDen N) :=
  ratApart0_of_pos (zDen_pos N)

def zOfNat (N : Nat) : Rat :=
  ratDivApart (zNum N) (zDen N) (zDen_apart0 N)

theorem zOfNat_nonneg
    {N : Nat}
    (_hN : 1 ≤ N) :
    ratLe ratZero (zOfNat N) := by
  unfold zOfNat
  have hnum : ratLe ratZero (zNum N) := by
    unfold zNum
    exact ratNat_nonneg (N - 1)
  exact ratDivApart_nonneg_of_nonneg_pos hnum (zDen_pos N) (zDen_apart0 N)

theorem zOfNat_lt_one
    {N : Nat}
    (_hN : 1 ≤ N) :
    ratLt (zOfNat N) ratOne := by
  unfold zOfNat
  have hden_pos : ratLt ratZero (zDen N) :=
    zDen_pos N
  have hcancel :
      RatEq
        (ratMul (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
          (zDen N))
        (zNum N) :=
    ratDivApart_mul_cancel_right (zDen_apart0 N)
  have hnum_lt_den : ratLt (zNum N) (zDen N) := by
    unfold zNum zDen
    exact ratNat_lt_of_nat_lt
      (Nat.lt_of_le_of_lt (Nat.sub_le N 1) (Nat.lt_succ_self N))
  apply ratLe_not_le_to_ratLt
  · have productLe :
        ratLe
          (ratMul
            (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
            (zDen N))
          (ratMul ratOne (zDen N)) :=
      ratLe_of_RatEq_left hcancel
        (ratLe_of_RatEq_right
          (ratLt_to_ratLe hnum_lt_den)
          (RatEq_symm (ratOne_mul_left (zDen N))))
    exact ratMul_le_cancel_right hden_pos productLe
  · intro oneLeZ
    have prodLe :
        ratLe (ratMul ratOne (zDen N))
          (ratMul
            (ratDivApart (zNum N) (zDen N) (zDen_apart0 N))
            (zDen N)) :=
      ratMul_le_mul_right oneLeZ (ratLt_to_ratLe hden_pos)
    have denLeNum :
        ratLe (zDen N) (zNum N) :=
      ratLe_of_RatEq_left (RatEq_symm (ratOne_mul_left (zDen N)))
        (ratLe_of_RatEq_right prodLe hcancel)
    exact ratLt_not_ratLe_reverse hnum_lt_den denLeNum

def lnLo (N M : Nat) : Rat :=
  twice (atanhPart (zOfNat N) M)

def lnHi
    (N M : Nat)
    (hN : 1 ≤ N) : Rat :=
  twice
    (ratAdd
      (atanhPart (zOfNat N) M)
      (atanhTailBound
        (zOfNat N)
        (zOfNat_nonneg hN)
        (zOfNat_lt_one hN)
        M))

def lnWidth
    (N M : Nat)
    (hN : 1 ≤ N) : Rat :=
  twice
    (atanhTailBound
      (zOfNat N)
      (zOfNat_nonneg hN)
      (zOfNat_lt_one hN)
      M)

theorem formal_lnN_enclosure
    (N M : Nat)
    (hN : 1 ≤ N) :
    SeriesEnclosedFrom
      (fun K => atanhFormalSeries (zOfNat N) K)
      M
      (lnLo N M)
      (lnHi N M hN) := by
  unfold lnLo lnHi
  exact atanh_full_enclosure
    (zOfNat N)
    (zOfNat_nonneg hN)
    (zOfNat_lt_one hN)
    M

inductive RatNumLnRealBridgeObligation : Type
  | analyticLogBridge

end BEDC.Real.RatNumLogEnclosure
