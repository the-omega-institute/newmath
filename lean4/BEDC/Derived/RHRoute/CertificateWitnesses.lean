import BEDC.Derived.RHRoute.AnalyticGombocForXi
import BEDC.Derived.RHRoute.TriAxisCoverage
import BEDC.Derived.RHRoute.WeilGramRoute

namespace BEDC.Derived.RHRoute.CertificateWitnesses

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.AnalyticGombocForXi
open BEDC.Derived.RHRoute.CausalReflectionPositiveCone
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.WeilGramRoute
open BEDC.Derived.RHRoute.WeilPositivityRoute
open BEDC.Foundations.TriAxisCoverage
open BEDC.Real.RatNumLogEnclosure

abbrev CertRat : Type :=
  RatNum

inductive ToyWitnessBoundary where
  | inhabitsDisplayedFields
  | notXiCertificate
  | notConstructiveRHProof

def toyWitnessBoundary : List ToyWitnessBoundary :=
  [ ToyWitnessBoundary.inhabitsDisplayedFields,
    ToyWitnessBoundary.notXiCertificate,
    ToyWitnessBoundary.notConstructiveRHProof ]

theorem toy_witness_boundary_count :
    toyWitnessBoundary.length = 3 := by
  rfl

theorem nat_tri_axis_projected_inhabited :
    Nonempty (TriAxisProjected Nat) := by
  exact ⟨natTriAxisProjected⟩

theorem int_tri_axis_projected_inhabited :
    Nonempty (TriAxisProjected Int) := by
  exact ⟨intTriAxisProjected⟩

def toyHerglotzPositivity : HerglotzPositivity where
  xi_log_derivative_real_part := fun _s => ratZero
  source_side_readback_obligations := canonicalHerglotzReadbackObligations
  source_side_readback_scope := rfl
  no_illegal_scale_source_sink := by
    intro _s _rightOfLine
    exact ratLe_refl ratZero
  right_half_plane_scope := by
    intro _s _rightOfLine
    exact ratLe_refl ratZero

theorem herglotz_positivity_inhabited :
    Nonempty HerglotzPositivity := by
  exact ⟨toyHerglotzPositivity⟩

def toyLocatedPositiveSpectralMeasure :
    LocatedPositiveSpectralMeasure where
  Atom := Unit
  mass := fun _a => ratZero
  spectral_location := fun _a => ratZero
  mass_nonnegative := by
    intro _a
    exact ratLe_refl ratZero
  location_nonnegative := by
    intro _a
    exact ratLe_refl ratZero
  cauchy_kernel := fun _x _a => ratZero
  kernel_nonnegative := by
    intro _x _hx _a
    exact ratLe_refl ratZero
  integral := fun _x => ratZero
  integral_nonnegative := by
    intro _x _hx
    exact ratLe_refl ratZero
  readback_obligations := canonicalStieltjesReadbackObligations
  readback_obligations_scope := rfl

def toyStieltjesPositiveSpectral :
    StieltjesPositiveSpectral where
  spectral_measure := toyLocatedPositiveSpectralMeasure
  dlog_xi_half_sqrt := fun _x => ratZero
  stieltjes_readback := by
    intro _x _hx
    exact RatEq_refl ratZero
  positive_spectral_measure := by
    intro _a
    exact ratLe_refl ratZero

theorem stieltjes_positive_spectral_inhabited :
    Nonempty StieltjesPositiveSpectral := by
  exact ⟨toyStieltjesPositiveSpectral⟩

def toyZeroWeilFunctional : FullWeilFunctional where
  value := fun _h => ratZero
  explicit_formula_obligations :=
    [ WeilExplicitFormulaObligation.primePowerDistributionMatchesVonMangoldt,
      WeilExplicitFormulaObligation.archimedeanGammaKernelMatchesXi,
      WeilExplicitFormulaObligation.polePairNormalizationMatchesCompletedZeta ]
  limit_obligations :=
    [ WeilLimitObligation.truncationsConvergeToFullDistribution,
      WeilLimitObligation.ratTestAlgebraSeparatesOffLineReflections,
      WeilLimitObligation.finiteEnclosuresRespectLocatedRealLimit ]

private theorem ratSub_self_eq_zero (x : CertRat) :
    RatEq (ratSub x x) ratZero := by
  exact (ratSub_zero_iff x x).mpr (RatEq_refl x)

private theorem ratSub_respects_local {x x' y y' : CertRat} :
    RatEq x x' -> RatEq y y' ->
      RatEq (ratSub x y) (ratSub x' y') := by
  intro xx' yy'
  unfold ratSub
  exact ratAdd_respects xx' (ratNeg_respects yy')

private def zeroWeilPrincipalMinorCertificate
    (size : Nat) (entry : Nat -> Nat -> CertRat)
    (entry_zero : forall i j : Nat, RatEq (entry i j) ratZero) :
    RationalPrincipalMinorPSDCertificate size entry where
  principalMinorValue := fun _indices => ratZero
  diagonal_minor_readback := by
    intro i _hi
    exact RatEq_symm (entry_zero i i)
  pair_minor_readback := by
    intro i j _hi _hj
    let diag := ratMul (entry i i) (entry j j)
    let off := ratMul (entry i j) (entry j i)
    have diagMulZero :
        RatEq diag (ratMul ratZero ratZero) :=
      ratMul_respects
        (x := entry i i) (x' := ratZero)
        (y := entry j j) (y' := ratZero)
        (entry_zero i i) (entry_zero j j)
    have offMulZero :
        RatEq off (ratMul ratZero ratZero) :=
      ratMul_respects
        (x := entry i j) (x' := ratZero)
        (y := entry j i) (y' := ratZero)
        (entry_zero i j) (entry_zero j i)
    have diagEqOff : RatEq diag off :=
      RatEq_trans _ _ _ diagMulZero (RatEq_symm offMulZero)
    have subDiagToOff : RatEq (ratSub diag diag) (ratSub diag off) :=
      ratSub_respects_local (RatEq_refl diag) diagEqOff
    exact RatEq_trans _ _ _
      (RatEq_refl ratZero)
      (RatEq_trans _ _ _
        (RatEq_symm (ratSub_self_eq_zero diag))
        subDiagToOff)
  principal_minor_nonnegative := by
    intro _indices _lengthOk _inside
    exact ratLe_refl ratZero

theorem toy_zero_weil_all_finite_gram_psd :
    AllFiniteWeilGramPSD toyZeroWeilFunctional := by
  intro ruler
  cases ruler with
  | mk size testAt =>
      cases size with
      | zero =>
          change True
          exact True.intro
      | succ n =>
          cases n with
          | zero =>
              change ratLe ratZero ratZero
              exact ratLe_refl ratZero
          | succ n =>
              cases n with
              | zero =>
                  change
                    ratLe ratZero ratZero ∧
                      ratLe ratZero ratZero ∧
                        ratLe
                          (ratMul ratZero ratZero)
                          (ratMul ratZero ratZero)
                  exact
                    ⟨ratLe_refl ratZero,
                      ⟨ratLe_refl ratZero,
                        ratLe_refl (ratMul ratZero ratZero)⟩⟩
              | succ m =>
                  let entry : Nat -> Nat -> CertRat :=
                    WeilGramMatrix toyZeroWeilFunctional
                      { size := Nat.succ (Nat.succ (Nat.succ m))
                        testAt := testAt }
                  have entry_zero :
                      forall i j : Nat, RatEq (entry i j) ratZero := by
                    intro _i _j
                    exact RatEq_refl ratZero
                  exact
                    Exists.intro
                      (zeroWeilPrincipalMinorCertificate
                        (Nat.succ (Nat.succ (Nat.succ m)))
                        entry entry_zero)
                      (by
                        intro _indices _lengthOk _inside
                        exact ratLe_refl ratZero)

def toyWeilGramReduction : WeilGramReduction where
  functional := toyZeroWeilFunctional
  all_finite_gram_psd := toy_zero_weil_all_finite_gram_psd

theorem weil_gram_reduction_inhabited :
    Nonempty WeilGramReduction := by
  exact ⟨toyWeilGramReduction⟩

theorem toy_weil_singleton_gram_psd
    (g : RatTestAlgebraElement) :
    PSD
      (singletonRuler g).size
      (WeilGramMatrix toyZeroWeilFunctional (singletonRuler g)) := by
  exact toy_zero_weil_all_finite_gram_psd (singletonRuler g)

theorem causal_reflection_positive_cone_nonempty_reads_constructive_rh :
    Nonempty CausalReflectionPositiveCone -> ConstructiveRH := by
  intro h
  cases h with
  | intro C =>
      exact CRPC_implies_RH C

theorem pick_hilbert_decomposition_nonempty_reads_constructive_rh :
    Nonempty PickHilbertDecomposition -> ConstructiveRH := by
  intro h
  cases h with
  | intro A =>
      exact rh_from_pick_hilbert_decomposition A

end BEDC.Derived.RHRoute.CertificateWitnesses
