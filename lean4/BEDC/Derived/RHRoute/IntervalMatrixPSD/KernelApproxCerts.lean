import BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanEntry
import BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly
import BEDC.Real.RatNumLogEnclosure

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel

namespace FormalK1

open BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly

def q (num den : Nat) : QRat :=
  qOfNatOverNat num den

def qz (num : Int) (den : Nat) : QRat :=
  qOfIntOverNat num den

def T1 : Poly :=
  [q 1 2, q 1 4, qz (-1) 48]

def A4 : Poly :=
  [qone, qzero, q 1 6, qzero, q 1 120]

def B1_4 : Poly :=
  [q 1 2, q 1 4, q 1 16, q 1 96, q 1 768]

def E1_4 : Poly :=
  sub B1_4 (mul A4 T1)

def E1_4_coeffs : Poly :=
  [qzero, qzero, qzero, qz (-1) 32, q 7 11520, qz (-1) 480, q 1 5760]

theorem E1_4_coeff :
    E1_4 = E1_4_coeffs := by
  rfl

end FormalK1

structure RawRatBound where
  num : Nat
  den : Nat

def RawRatBound.crossLe (x y : RawRatBound) : Prop :=
  x.num * y.den <= y.num * x.den

theorem RawRatBound.crossLe_refl (x : RawRatBound) :
    x.crossLe x := by
  unfold RawRatBound.crossLe
  exact Nat.le_refl _

def qNat (num den : Nat) : BRat :=
  match den with
  | 0 => ratZero
  | Nat.succ d =>
      ratDivApart (ratNat num) (ratNat (Nat.succ d))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos d))

def qInt (num : Int) (den : Nat) : BRat :=
  match num with
  | Int.ofNat n => qNat n den
  | Int.negSucc n => ratNeg (qNat (Nat.succ n) den)

theorem qNat_nonneg (num den : Nat) :
    ratLe ratZero (qNat num den) := by
  cases den with
  | zero =>
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | succ d =>
      change
        ratLe ratZero
          (ratDivApart (ratNat num) (ratNat (Nat.succ d))
            (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos
              (Nat.succ_pos d)))
      exact ratDivApart_nonneg_of_nonneg_pos
        (ratNat_nonneg num)
        (BEDC.Real.RatNumLogEnclosure.ratNat_pos_of_pos (Nat.succ_pos d))
        (BEDC.Real.RatNumLogEnclosure.ratNat_apart0_of_pos (Nat.succ_pos d))

def RawRatBound.toRat (x : RawRatBound) : BRat :=
  qNat x.num x.den

def zeroPanelLeft : BRat :=
  ratZero

def zeroPanelRight : BRat :=
  qNat 1 8

def K1_T : ArchPoly :=
  [qNat 1 2, qNat 1 4, qInt (-1) 48]

def K1_eps : BRat :=
  qNat 1 10000

theorem K1_eps_nonneg :
    ratLe ratZero K1_eps :=
  qNat_nonneg 1 10000

def K1_A4 : ArchPoly :=
  [ratOne, ratZero, qNat 1 6, ratZero, qNat 1 120]

def K1_B1_4 : ArchPoly :=
  [qNat 1 2, qNat 1 4, qNat 1 16, qNat 1 96, qNat 1 768]

def K1_E1_4 : ArchPoly :=
  [ratZero, ratZero, ratZero, qInt (-1) 32, qNat 7 11520,
    qInt (-1) 480, qNat 1 5760]

theorem K1_E1_4_coeff :
    K1_E1_4 =
      [ratZero, ratZero, ratZero, qInt (-1) 32, qNat 7 11520,
        qInt (-1) 480, qNat 1 5760] := by
  rfl

def K1_E1_4_abs_bound : BRat :=
  qNat 30827 503316480

def K1_A_tail4_bound : BRat :=
  qNat 1 1320919040

def K1_B1_tail4_bound : BRat :=
  qNat 1 249036800

def K1_T_abs_bound : BRat :=
  qNat 1633 3072

def K1_combined_error_bound : BRat :=
  qNat 94450105033 1541988050534400

def K1_E1_4_abs_bound_raw : RawRatBound :=
  { num := 30827, den := 503316480 }

def K1_A_tail4_bound_raw : RawRatBound :=
  { num := 1, den := 1320919040 }

def K1_B1_tail4_bound_raw : RawRatBound :=
  { num := 1, den := 249036800 }

def K1_T_abs_bound_raw : RawRatBound :=
  { num := 1633, den := 3072 }

def K1_combined_error_bound_raw : RawRatBound :=
  { num := 94450105033, den := 1541988050534400 }

def K1_eps_raw : RawRatBound :=
  { num := 1, den := 10000 }

def K1_raw_error_budget_slack : Nat :=
  597487000204400

def K1_T_abs_unreduced_raw : RawRatBound :=
  { num := 1633, den := 3072 }

def K1_E1_4_abs_unreduced_raw : RawRatBound :=
  { num := 92481, den := 1509949440 }

theorem K1_T_abs_bound_raw_term_sum :
    1 * 1536 + 1 * 96 + 1 = K1_T_abs_unreduced_raw.num := by
  rfl

theorem K1_T_abs_bound_raw_den_readback :
    K1_T_abs_unreduced_raw.den = K1_T_abs_bound_raw.den := by
  rfl

theorem K1_T_abs_bound_raw_num_readback :
    K1_T_abs_unreduced_raw.num = K1_T_abs_bound_raw.num := by
  rfl

theorem K1_E1_4_abs_bound_raw_term_sum :
    92160 + 224 + 96 + 1 = K1_E1_4_abs_unreduced_raw.num := by
  rfl

theorem K1_E1_4_abs_bound_raw_reduction :
    K1_E1_4_abs_unreduced_raw.num * K1_E1_4_abs_bound_raw.den =
      K1_E1_4_abs_bound_raw.num * K1_E1_4_abs_unreduced_raw.den := by
  rfl

theorem K1_combined_error_bound_raw_term_sum :
    94443292685 + 6191808 + 620540 =
      K1_combined_error_bound_raw.num := by
  rfl

theorem K1_combined_error_bound_raw_den_scale_E :
    K1_E1_4_abs_bound_raw.den * 3063655 =
      K1_combined_error_bound_raw.den := by
  rfl

theorem K1_combined_error_bound_raw_den_scale_B1 :
    K1_B1_tail4_bound_raw.den * 6191808 =
      K1_combined_error_bound_raw.den := by
  rfl

theorem K1_combined_error_bound_raw_den_scale_AT :
    4057863290880 * 380 = K1_combined_error_bound_raw.den := by
  rfl

theorem K1_E1_4_abs_bound_raw_readback :
    K1_E1_4_abs_bound = K1_E1_4_abs_bound_raw.toRat := by
  rfl

theorem K1_A_tail4_bound_raw_readback :
    K1_A_tail4_bound = K1_A_tail4_bound_raw.toRat := by
  rfl

theorem K1_B1_tail4_bound_raw_readback :
    K1_B1_tail4_bound = K1_B1_tail4_bound_raw.toRat := by
  rfl

theorem K1_T_abs_bound_raw_readback :
    K1_T_abs_bound = K1_T_abs_bound_raw.toRat := by
  rfl

theorem K1_combined_error_bound_raw_readback :
    K1_combined_error_bound = K1_combined_error_bound_raw.toRat := by
  rfl

theorem K1_eps_raw_readback :
    K1_eps = K1_eps_raw.toRat := by
  rfl

theorem K1_raw_error_budget_cert :
    K1_combined_error_bound_raw.crossLe K1_eps_raw := by
  unfold RawRatBound.crossLe K1_combined_error_bound_raw K1_eps_raw
  exact Nat.le.intro
    (show
      94450105033 * 10000 + K1_raw_error_budget_slack =
        1 * 1541988050534400 by
      rfl)

inductive K1ZeroPanelAnalyticObligation where
  | desingularizedKernelMatchesLocatedExpression
  | sinhcTaylorTail
  | halfExpTaylorTail
  | normalizedResidualBoundReadback
  | combinedErrorRatLeReadback
deriving DecidableEq, Repr

def K1_zeroPanel_obligations : List K1ZeroPanelAnalyticObligation :=
  [ K1ZeroPanelAnalyticObligation.desingularizedKernelMatchesLocatedExpression,
    K1ZeroPanelAnalyticObligation.sinhcTaylorTail,
    K1ZeroPanelAnalyticObligation.halfExpTaylorTail,
    K1ZeroPanelAnalyticObligation.normalizedResidualBoundReadback,
    K1ZeroPanelAnalyticObligation.combinedErrorRatLeReadback ]

theorem K1_zeroPanel_obligations_readback :
    K1_zeroPanel_obligations.length = 5 := by
  rfl

class K1ZeroPanelObligations where
  A : BRat -> BRat
  B1 : BRat -> BRat
  K1 : BRat -> BRat
  A_tail4_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe ratZero (ratSub (A t) (evalPoly K1_A4 t)) ∧
        ratLe (ratSub (A t) (evalPoly K1_A4 t)) K1_A_tail4_bound
  B1_tail4_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe ratZero (ratSub (B1 t) (evalPoly K1_B1_4 t)) ∧
        ratLe (ratSub (B1 t) (evalPoly K1_B1_4 t)) K1_B1_tail4_bound
  A_ge_one_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe ratOne (A t)
  T1_abs_bound_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe (ratAbs (evalPoly K1_T t)) K1_T_abs_bound
  E1_4_abs_bound_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe (ratAbs (evalPoly K1_E1_4 t)) K1_E1_4_abs_bound
  E1_4_polynomial_identity :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      RatEq
        (evalPoly K1_E1_4 t)
        (ratSub (evalPoly K1_B1_4 t)
          (ratMul (evalPoly K1_A4 t) (evalPoly K1_T t)))
  normalized_kernel_error_bound :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe
        (ratAbs (ratSub (K1 t) (evalPoly K1_T t)))
        (ratAbs
          (ratSub (B1 t)
            (ratMul (A t) (evalPoly K1_T t))))
  residual_bound_from_tails :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe
        (ratAbs
          (ratSub (B1 t)
            (ratMul (A t) (evalPoly K1_T t))))
        K1_combined_error_bound
  combined_error_le_eps : ratLe K1_combined_error_bound K1_eps
  analytic_obligations :
    K1_zeroPanel_obligations =
      [ K1ZeroPanelAnalyticObligation.desingularizedKernelMatchesLocatedExpression,
        K1ZeroPanelAnalyticObligation.sinhcTaylorTail,
        K1ZeroPanelAnalyticObligation.halfExpTaylorTail,
        K1ZeroPanelAnalyticObligation.normalizedResidualBoundReadback,
        K1ZeroPanelAnalyticObligation.combinedErrorRatLeReadback ]

def K1 [O : K1ZeroPanelObligations] : BRat -> BRat :=
  O.K1

theorem A_tail4_zeroPanel
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe ratZero (ratSub (O.A t) (evalPoly K1_A4 t)) ∧
      ratLe (ratSub (O.A t) (evalPoly K1_A4 t)) K1_A_tail4_bound :=
  O.A_tail4_zeroPanel t ht

theorem B1_tail4_zeroPanel
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe ratZero (ratSub (O.B1 t) (evalPoly K1_B1_4 t)) ∧
      ratLe (ratSub (O.B1 t) (evalPoly K1_B1_4 t)) K1_B1_tail4_bound :=
  O.B1_tail4_zeroPanel t ht

theorem A_ge_one_zeroPanel
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe ratOne (O.A t) :=
  O.A_ge_one_zeroPanel t ht

theorem T1_abs_bound_zeroPanel
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe (ratAbs (evalPoly K1_T t)) K1_T_abs_bound :=
  O.T1_abs_bound_zeroPanel t ht

theorem E1_4_abs_bound_zeroPanel
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe (ratAbs (evalPoly K1_E1_4 t)) K1_E1_4_abs_bound :=
  O.E1_4_abs_bound_zeroPanel t ht

theorem K1_zeroPanel_sound
    [O : K1ZeroPanelObligations]
    (t : BRat) (ht : inClosedPanel zeroPanelLeft zeroPanelRight t) :
    ratLe (ratAbs (ratSub (K1 t) (evalPoly K1_T t))) K1_eps :=
  ratLe_trans (O.normalized_kernel_error_bound t ht)
    (ratLe_trans (O.residual_bound_from_tails t ht)
      O.combined_error_le_eps)

def K1_zeroPanel_approx
    [K1ZeroPanelObligations] :
    KernelApprox K1 zeroPanelLeft zeroPanelRight where
  T := K1_T
  eps := K1_eps
  eps_nonneg := K1_eps_nonneg
  sound := K1_zeroPanel_sound

end BEDC.Derived.RHRoute.IntervalMatrixPSD
