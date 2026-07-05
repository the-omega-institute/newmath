import BEDC.Real.RatNumKernel
import BEDC.Real.RatNumLogEnclosure
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.PZGLedgerClosure

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  ZetaBoxEvaluator.RatComplex

def scalingLedger (delta len : Rat) : Rat :=
  ratMul delta len

private theorem ratNum_zero_to_RatEq_zero {x : Rat}
    (numZero : IntEq x.num intZero) :
    RatEq x ratZero := by
  unfold RatEq
  change IntEq
    (IntMul x.num (ratDenInt ratZero))
    (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem ratEq_zero_of_mul_left_zero (len : Rat) :
    RatEq (scalingLedger ratZero len) ratZero := by
  unfold scalingLedger
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero len.num) intZero
  exact intMul_zero_left len.num

private theorem ratApart0_not_RatEq_zero {x : Rat} :
    ratApart0 x -> RatEq x ratZero -> False := by
  intro hx hzero
  exact intApart0_not_zero_pair hx (RatEq_zero_num hzero)

private theorem ratMul_right_cancel_apart0_local (x y c : Rat)
    (hc : ratApart0 c)
    (h : RatEq (ratMul x c) (ratMul y c)) :
    RatEq x y :=
  BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0 x y c hc h

private theorem ratMul_left_cancel_apart0_local (c x y : Rat)
    (hc : ratApart0 c)
    (h : RatEq (ratMul c x) (ratMul c y)) :
    RatEq x y := by
  have swapped :
      RatEq (ratMul x c) (ratMul y c) :=
    RatEq_trans _ _ _
      (RatEq_symm (ratMul_comm c x))
      (RatEq_trans _ _ _ h (ratMul_comm c y))
  exact ratMul_right_cancel_apart0_local x y c hc swapped

theorem ledger_zero_iff_offset_zero (delta len : Rat)
    (hlen : ratApart0 len) :
    RatEq (scalingLedger delta len) ratZero ↔ RatEq delta ratZero := by
  constructor
  · intro hzero
    have hscaled :
        RatEq (ratMul delta len) (ratMul ratZero len) :=
      RatEq_trans _ _ _
        hzero
        (RatEq_symm (ratEq_zero_of_mul_left_zero len))
    exact ratMul_right_cancel_apart0_local delta ratZero len hlen hscaled
  · intro hdelta
    exact RatEq_trans _ _ _
      (ratMul_respects hdelta (RatEq_refl len))
      (ratEq_zero_of_mul_left_zero len)

theorem local_closure_iff_offset_zero {delta : Rat} {len : Rat}
    (hlen : ratLt ratZero len) :
    RatEq (scalingLedger delta len) ratZero ↔ RatEq delta ratZero :=
  ledger_zero_iff_offset_zero delta len (ratApart0_of_pos hlen)

theorem offline_ledger_ne_zero (delta len : Rat)
    (hd : ratApart0 delta) (hl : ratApart0 len) :
    RatEq (scalingLedger delta len) ratZero -> False := by
  intro hzero
  exact ratApart0_not_RatEq_zero (ratMul_apart0 hd hl) hzero

theorem offline_ledger_sign (delta len : Rat)
    (hl : ratLt ratZero len) :
    (ratLt ratZero delta -> ratLt ratZero (scalingLedger delta len)) ∧
      (ratLt delta ratZero -> ratLt (scalingLedger delta len) ratZero) := by
  constructor
  · intro hd
    have raw :
        ratLt (ratMul ratZero len) (ratMul delta len) :=
      ratMul_lt_mul_right hd hl
    exact ratLt_of_RatEq_left
      (RatEq_symm (ratEq_zero_of_mul_left_zero len)) raw
  · intro hd
    have raw :
        ratLt (ratMul delta len) (ratMul ratZero len) :=
      ratMul_lt_mul_right hd hl
    exact ratLt_of_RatEq_right raw (ratEq_zero_of_mul_left_zero len)

theorem no_global_register_cancels {delta len1 len2 : Rat}
    (hd : ratApart0 delta) (hne : RatEq len1 len2 -> False) :
    RatEq (scalingLedger delta len1) (scalingLedger delta len2) -> False := by
  intro hsame
  exact hne (ratMul_left_cancel_apart0_local delta len1 len2 hd hsame)

/- A scalar depending only on `s` cannot supply account-by-account cancellation:
if `delta` is apart from zero, multiplication by `delta` is injective on the
ledger length coordinate. -/

def ledgerOnRay (delta len : Rat) (m : Nat) : Rat :=
  scalingLedger delta (ratMul (ratNat m) len)

theorem offline_ledger_ray_nonzero (delta len : Rat)
    (hd : ratApart0 delta) (hl : ratApart0 len) :
    ∀ m : Nat, 0 < m ->
      RatEq (ledgerOnRay delta len m) ratZero -> False := by
  intro m hm hzero
  unfold ledgerOnRay scalingLedger at hzero
  exact ratApart0_not_RatEq_zero
    (ratMul_apart0 hd (ratMul_apart0 (ratNat_apart0_of_pos hm) hl))
    hzero

theorem offline_ledger_ray_succ_nonzero (delta len : Rat)
    (hd : ratApart0 delta) (hl : ratApart0 len) :
    ∀ m : Nat,
      RatEq (ledgerOnRay delta len (Nat.succ m)) ratZero -> False := by
  intro m
  exact offline_ledger_ray_nonzero delta len hd hl (Nat.succ m) (Nat.succ_pos m)

theorem offline_ledger_ray_strictly_increases (delta len : Rat)
    (hd : ratLt ratZero delta) (hl : ratLt ratZero len) :
    ∀ m : Nat,
      ratLt (ledgerOnRay delta len m)
        (ledgerOnRay delta len (Nat.succ m)) := by
  intro m
  unfold ledgerOnRay scalingLedger
  have hNat : ratLt (ratNat m) (ratNat (Nat.succ m)) :=
    ratNat_lt_of_nat_lt (Nat.lt_succ_self m)
  have hLen :
      ratLt (ratMul (ratNat m) len)
        (ratMul (ratNat (Nat.succ m)) len) :=
    ratMul_lt_mul_right hNat hl
  exact ratMul_lt_mul_left hLen hd

/- The ray result is the kernel-level substitute for the archimedean
unboundedness reading: every positive step is nonzero, and the ledger values
strictly increase.  A full bound-escape theorem requires a dedicated rational
archimedean amplifier. -/

theorem offline_ledger_unbounded_progression (delta len : Rat)
    (hd : ratLt ratZero delta) (hl : ratLt ratZero len) :
    (∀ m : Nat,
      RatEq (ledgerOnRay delta len (Nat.succ m)) ratZero -> False) ∧
      (∀ m : Nat,
        ratLt (ledgerOnRay delta len m)
          (ledgerOnRay delta len (Nat.succ m))) :=
  ⟨offline_ledger_ray_succ_nonzero delta len
      (ratApart0_of_pos hd) (ratApart0_of_pos hl),
    offline_ledger_ray_strictly_increases delta len hd hl⟩

def emptyAccountCoeff : RatComplex :=
  ratComplexOne

theorem labeled_vector_nonzero :
    emptyAccountCoeff = ratComplexZero -> False := by
  intro h
  have hRe : RatEq ratOne ratZero := by
    have hReEq : ratComplexOne.re = ratComplexZero.re :=
      congrArg RatComplex.re h
    exact Eq.ndrec (RatEq_refl ratOne) hReEq
  exact ratApart0_not_RatEq_zero ratOne_apart hRe

structure PZGSystem where
  isZero : Rat -> Prop
  offsetOf : Rat -> Rat

def IsSystemZero (Sys : PZGSystem) (s : Rat) : Prop :=
  Sys.isZero s

def LedgerClosureBridge (Sys : PZGSystem) : Prop :=
  ∀ s : Rat, Sys.isZero s ->
    ∀ len : Rat, ratLt ratZero len ->
      RatEq (scalingLedger (Sys.offsetOf s) len) ratZero

/- `LedgerClosureBridge` is the named hinge from projected system zeros to
ledger closure.  This module records it as an obligation and only proves the
conditional readback below. -/

theorem system_rh_of_bridge (Sys : PZGSystem)
    (h : LedgerClosureBridge Sys) (s : Rat) (hz : Sys.isZero s)
    (len : Rat) (hl : ratLt ratZero len) :
    RatEq (Sys.offsetOf s) ratZero :=
  (local_closure_iff_offset_zero (delta := Sys.offsetOf s) (len := len) hl).mp
    (h s hz len hl)

end BEDC.Derived.RHRoute.PZGLedgerClosure
