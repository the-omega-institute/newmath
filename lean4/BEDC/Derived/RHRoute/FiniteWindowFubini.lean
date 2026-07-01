import BEDC.Derived.RHRoute.FiniteEulerDirichlet

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.FiniteWindowFubini

open BEDC.Derived.PrimeUp
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.HalfPlaneEulerProduct
open BEDC.Derived.RHRoute.QPrimeLocated
open BEDC.Derived.RHRoute.FiniteEulerDirichlet
open BEDC.Real.RatNumKernel

abbrev Rat : Type :=
  HalfPlaneEulerProduct.Rat

abbrev RatComplex : Type :=
  HalfPlaneEulerProduct.RatComplex

def qGeomInclusive
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (K : Nat) : Rat :=
  geomSum (qPrime_localSchurContractive p hp s h).radius (Nat.succ K)

structure FiniteWindowDirichletLocated
    (N : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s) where
  support_terms : List FormalEulerTerm
  support_terms_eq : support_terms = encodedDirichletTerms window
  every_prime_located :
    ∀ p K, (p, K) ∈ window -> (hp : IsPrime p) ->
      QPrimeLocated p hp s h
  all_terms_from_finite_window :
    support_terms = encodedDirichletTerms window
  smooth_cutoff : Nat
  smooth_cutoff_eq : smooth_cutoff = N

def finiteWindowDirichletLocated
    (N : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s)
    (located :
      ∀ p K, (p, K) ∈ window -> (hp : IsPrime p) ->
        QPrimeLocated p hp s h) :
    FiniteWindowDirichletLocated N window s h :=
  { support_terms := encodedDirichletTerms window
    support_terms_eq := rfl
    every_prime_located := located
    all_terms_from_finite_window := rfl
    smooth_cutoff := N
    smooth_cutoff_eq := rfl }

theorem finiteWindow_partial_dirichlet_located
    (N : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s)
    (located :
      ∀ p K, (p, K) ∈ window -> (hp : IsPrime p) ->
        QPrimeLocated p hp s h) :
    (finiteWindowDirichletLocated N window s h located).support_terms =
      encodedDirichletTerms window := by
  rfl

theorem finiteWindow_fubini_exact
    (window : List (Nat × Nat)) :
    eulerExpandTerms window = encodedDirichletTerms window := by
  exact finiteEuler_eq_encodedDirichlet window

def finiteWindowTruncationErrorBound
    (q : Rat) (K : Nat) (hq1 : ratLt q ratOne) : Rat :=
  ratDivApart (ratPow q (Nat.succ K)) (ratSub ratOne q)
    (ratApart0_of_pos (sub_pos_of_lt hq1))

inductive FiniteWindowTruncationResidualKind where
  | dividedTailAbsReadback
  | complexModulusToRatRadius

theorem finiteWindow_geom_truncation_error
    (q : Rat) (hq1 : ratLt q ratOne) (K : Nat) :
    ratLe
      (ratSub
        (ratDivApart ratOne (ratSub ratOne q)
          (ratApart0_of_pos (sub_pos_of_lt hq1)))
        (geomSum q (Nat.succ K)))
      (finiteWindowTruncationErrorBound q K hq1) := by
  unfold finiteWindowTruncationErrorBound
  exact geomSum_truncation_error_le_tail_div q (Nat.succ K)
    (ratApart0_of_pos (sub_pos_of_lt hq1))

theorem finiteWindow_geom_truncation_telescope
    (q : Rat) (_hq1 : ratLt q ratOne) (K : Nat) :
    RatEq
      (ratAdd
        (ratMul (ratSub ratOne q) (geomSum q (Nat.succ K)))
        (ratPow q (Nat.succ K)))
      ratOne :=
  geom_telescopes q (Nat.succ K)

theorem finiteWindow_geom_sum_le_inverse
    (q : Rat) (hq0 : ratLe ratZero q) (hq1 : ratLt q ratOne) (K : Nat) :
    ratLe (geomSum q (Nat.succ K))
      (ratDivApart ratOne (ratSub ratOne q)
        (ratApart0_of_pos (sub_pos_of_lt hq1))) :=
  geomSum_le_inv_one_sub q hq0 hq1 (Nat.succ K)
    (ratApart0_of_pos (sub_pos_of_lt hq1))

structure FiniteWindowGeomTruncationCertificate
    (q : Rat) (K : Nat) (hq1 : ratLt q ratOne) where
  error_bound : Rat
  error_bound_eq :
    error_bound = finiteWindowTruncationErrorBound q K hq1
  error_le_bound :
    ratLe
      (ratSub
        (ratDivApart ratOne (ratSub ratOne q)
          (ratApart0_of_pos (sub_pos_of_lt hq1)))
        (geomSum q (Nat.succ K)))
      error_bound
  telescope_exact :
    RatEq
      (ratAdd
        (ratMul (ratSub ratOne q) (geomSum q (Nat.succ K)))
        (ratPow q (Nat.succ K)))
      ratOne
  finite_sum_le_inverse :
    (hq0 : ratLe ratZero q) ->
      ratLe (geomSum q (Nat.succ K))
        (ratDivApart ratOne (ratSub ratOne q)
          (ratApart0_of_pos (sub_pos_of_lt hq1)))
  residual_readbacks : List FiniteWindowTruncationResidualKind
  residual_readbacks_eq :
    residual_readbacks =
      [ FiniteWindowTruncationResidualKind.dividedTailAbsReadback,
        FiniteWindowTruncationResidualKind.complexModulusToRatRadius ]

def finiteWindowGeomTruncationCertificate
    (q : Rat) (hq1 : ratLt q ratOne) (K : Nat) :
    FiniteWindowGeomTruncationCertificate q K hq1 :=
  { error_bound := finiteWindowTruncationErrorBound q K hq1
    error_bound_eq := rfl
    error_le_bound := finiteWindow_geom_truncation_error q hq1 K
    telescope_exact := finiteWindow_geom_truncation_telescope q hq1 K
    finite_sum_le_inverse := by
      intro hq0
      exact finiteWindow_geom_sum_le_inverse q hq0 hq1 K
    residual_readbacks :=
      [ FiniteWindowTruncationResidualKind.dividedTailAbsReadback,
        FiniteWindowTruncationResidualKind.complexModulusToRatRadius ]
    residual_readbacks_eq := rfl }

def finiteWindow_qPrime_geom_truncation_error
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (located : QPrimeLocated p hp s h) (K : Nat) :
    FiniteWindowGeomTruncationCertificate
      (qPrimeLocatedAbs located) K located.abs_lt_one := by
  exact finiteWindowGeomTruncationCertificate
    (qPrimeLocatedAbs located) located.abs_lt_one K

theorem finiteWindow_qPrime_geom_sum_le_inverse
    (p : Nat) (hp : IsPrime p) (s : RatComplex) (h : HP1WitnessRat s)
    (located : QPrimeLocated p hp s h) (K : Nat) :
    ratLe (geomSum (qPrimeLocatedAbs located) (Nat.succ K))
      (ratDivApart ratOne
        (ratSub ratOne (qPrimeLocatedAbs located))
        (ratApart0_of_pos (sub_pos_of_lt located.abs_lt_one))) := by
  exact finiteWindow_geom_sum_le_inverse
    (qPrimeLocatedAbs located)
    (by
      rw [qPrimeLocated_abs_eq located]
      exact located.radial.radius_nonneg)
    located.abs_lt_one
    K

inductive FiniteWindowFubiniResidualObligationKind where
  | infinitePrimeWindowLimit
  | infiniteTailDirichletLimit
  | analyticEulerDirichletBridge
  | dividedTailAbsReadback
  | complexModulusToRatRadius

structure FiniteWindowFubiniFinitePart
    (N K : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s) where
  located_dirichlet : FiniteWindowDirichletLocated N window s h
  fubini_exact : eulerExpandTerms window = encodedDirichletTerms window
  local_truncation_bound :
    ∀ p E, (member : (p, E) ∈ window) -> (hp : IsPrime p) ->
      let located := located_dirichlet.every_prime_located p E member hp
      FiniteWindowGeomTruncationCertificate
        (qPrimeLocatedAbs located) K located.abs_lt_one
  local_finite_sum_le_inverse :
    ∀ p E, (member : (p, E) ∈ window) -> (hp : IsPrime p) ->
      let located := located_dirichlet.every_prime_located p E member hp
      ratLe (geomSum (qPrimeLocatedAbs located) (Nat.succ K))
        (ratDivApart ratOne
          (ratSub ratOne (qPrimeLocatedAbs located))
          (ratApart0_of_pos (sub_pos_of_lt located.abs_lt_one)))

structure FiniteWindowFubiniCertificate
    (N K : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s) where
  finite_part : FiniteWindowFubiniFinitePart N K window s h
  residual_obligations : List FiniteWindowFubiniResidualObligationKind
  residual_obligations_eq :
    residual_obligations =
      [ FiniteWindowFubiniResidualObligationKind.infinitePrimeWindowLimit,
        FiniteWindowFubiniResidualObligationKind.infiniteTailDirichletLimit,
        FiniteWindowFubiniResidualObligationKind.analyticEulerDirichletBridge,
        FiniteWindowFubiniResidualObligationKind.dividedTailAbsReadback,
        FiniteWindowFubiniResidualObligationKind.complexModulusToRatRadius ]
  convergence_obligation : EffectiveConvergenceObligation
  convergence_obligation_kind :
    convergence_obligation.kind =
      EulerDirichletObligationKind.infiniteEulerToZetaEffectiveConvergence

def finiteWindowFubiniCertificate
    (N K : Nat) (window : List (Nat × Nat)) (s : RatComplex)
    (h : HP1WitnessRat s)
    (located :
      ∀ p E, (p, E) ∈ window -> (hp : IsPrime p) ->
        QPrimeLocated p hp s h) :
    FiniteWindowFubiniCertificate N K window s h :=
  { finite_part :=
      { located_dirichlet :=
          finiteWindowDirichletLocated N window s h located
        fubini_exact := finiteWindow_fubini_exact window
        local_truncation_bound := by
          intro p E member hp
          exact finiteWindow_qPrime_geom_truncation_error p hp s h
            (located p E member hp) K
        local_finite_sum_le_inverse := by
          intro p E member hp
          exact finiteWindow_qPrime_geom_sum_le_inverse p hp s h
            (located p E member hp) K }
    residual_obligations :=
      [ FiniteWindowFubiniResidualObligationKind.infinitePrimeWindowLimit,
        FiniteWindowFubiniResidualObligationKind.infiniteTailDirichletLimit,
        FiniteWindowFubiniResidualObligationKind.analyticEulerDirichletBridge,
        FiniteWindowFubiniResidualObligationKind.dividedTailAbsReadback,
        FiniteWindowFubiniResidualObligationKind.complexModulusToRatRadius ]
    residual_obligations_eq := rfl
    convergence_obligation := infiniteEulerZetaConvergenceObligation
    convergence_obligation_kind := rfl }

def toyWindowSixKThree : List (Nat × Nat) :=
  [(2, 3), (3, 3), (5, 3)]

private theorem natOne_strict_of_tail (tail : BHist) :
    UnaryHistory tail -> (tail = BHist.Empty -> False) ->
      NatUnaryStrictPrefix NatOneLocal (BHist.e1 tail) := by
  intro tailUnary tailNonempty
  have shifted : append NatOneLocal tail = BHist.e1 tail :=
    (unary_append_e1_left (h := tail) (k := BHist.Empty) tailUnary).trans
      (congrArg BHist.e1 (append_empty_left tail))
  exact ⟨tail, tailUnary, tailNonempty, cont_intro shifted.symm⟩

private theorem natOne_strict_natToUnary_succ_succ (n : Nat) :
    NatUnaryStrictPrefix NatOneLocal
      (BEDC.Derived.IntUp.natToUnary (Nat.succ (Nat.succ n))) := by
  change NatUnaryStrictPrefix NatOneLocal
    (BHist.e1 (BEDC.Derived.IntUp.natToUnary (Nat.succ n)))
  exact natOne_strict_of_tail (BEDC.Derived.IntUp.natToUnary (Nat.succ n))
    (BEDC.Derived.IntUp.natToUnary_unary (Nat.succ n)) (fun empty => by
      change BHist.e1 (BEDC.Derived.IntUp.natToUnary n) = BHist.Empty at empty
      exact not_hsame_e1_empty empty)

theorem five_isPrime : IsPrime 5 := by
  have large : NatUnaryStrictPrefix NatOneLocal
      (BEDC.Derived.IntUp.natToUnary 5) :=
    natOne_strict_natToUnary_succ_succ 3
  change NatPrime (minFactor (BEDC.Derived.IntUp.natToUnary 5) large)
  exact minFactor_prime large

theorem toyWindowSixKThree_all_prime :
    ∀ p K, (p, K) ∈ toyWindowSixKThree -> IsPrime p := by
  intro p K member
  unfold toyWindowSixKThree at member
  cases member with
  | head =>
      exact FiniteEulerDirichlet.two_isPrime
  | tail _ memberTail =>
      cases memberTail with
      | head =>
          exact three_isPrime
      | tail _ memberTailTail =>
          cases memberTailTail with
          | head =>
              exact five_isPrime
          | tail _ emptyMember =>
              cases emptyMember

theorem toy_finiteWindow_fubini_exact :
    eulerExpandTerms toyWindowSixKThree =
      encodedDirichletTerms toyWindowSixKThree := by
  exact finiteWindow_fubini_exact toyWindowSixKThree

theorem toy_finiteWindow_fubini_exact_term_count :
    (encodedDirichletTerms toyWindowSixKThree).length = 64 := by
  rfl

def toyPrimeRadialLocated
    (p : Nat) (hp : IsPrime p) :
    QPrimeRadialLocated p hp toyTwoPoint :=
  { exp_input := qPrimeExpInput p toyTwoPoint
    exp_input_eq := rfl
    radius := primeUnitRadius p hp
    radius_nonneg := ratLt_to_ratLe (primeUnitRadius_pos hp)
    radius_lt_one := primeUnitRadius_lt_one hp
    unit_majorant := ratLe_refl (primeUnitRadius p hp)
    log_enclosure :=
      BEDC.Real.RatNumLogEnclosure.formal_lnN_enclosure p
        (BEDC.Real.RatNumLogEnclosure.lnM96 p)
        (Nat.le_of_lt (prime_nat_gt_one hp))
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.logNatLocated,
        QPrimeAnalyticBridgeObligation.expNegRealLog,
        QPrimeAnalyticBridgeObligation.halfPlaneUnitMajorant ]
    bridge_obligations_eq := rfl }

def toyPrimePhaseLocated (p : Nat) :
    QPrimePhaseLocated p toyTwoPoint :=
  { phase := qPrimePhaseCenter p toyTwoPoint
    phase_eq := rfl
    cos := qPoint ratOne
    sin := qPoint ratZero
    cos_ordered := qPoint_ordered ratOne
    sin_ordered := qPoint_ordered ratZero
    bridge_obligations :=
      [ QPrimeAnalyticBridgeObligation.phaseLogProduct,
        QPrimeAnalyticBridgeObligation.sinCosPhase ]
    bridge_obligations_eq := rfl }

def toyQPrimeLocated
    (p : Nat) (hp : IsPrime p) :
    QPrimeLocated p hp toyTwoPoint toyHP1 :=
  assembleQPrimeLocated (toyPrimeRadialLocated p hp)
    (toyPrimePhaseLocated p)

def toyLocatedProviderSixKThree :
    ∀ p K, (p, K) ∈ toyWindowSixKThree -> (hp : IsPrime p) ->
      QPrimeLocated p hp toyTwoPoint toyHP1 := by
  intro p _K _member hp
  exact toyQPrimeLocated p hp

theorem toy_finiteWindow_fubini_certificate_exists :
    ∃ cert : FiniteWindowFubiniCertificate 6 3 toyWindowSixKThree toyTwoPoint toyHP1,
      cert.finite_part.fubini_exact = toy_finiteWindow_fubini_exact := by
  exact
    ⟨finiteWindowFubiniCertificate 6 3 toyWindowSixKThree toyTwoPoint toyHP1
      toyLocatedProviderSixKThree, rfl⟩

end BEDC.Derived.RHRoute.FiniteWindowFubini
