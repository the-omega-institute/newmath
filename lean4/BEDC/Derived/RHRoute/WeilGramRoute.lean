import BEDC.Derived.RHRoute.WeilPositivityRoute

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.WeilGramRoute

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.WeilPositivityRoute
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

def WeilBilinearArgument
    (g h : RatTestFunction) : RatTestFunction :=
  RatTestFunction.convolution g h.sharp

structure FiniteWeilRuler where
  size : Nat
  testAt : Nat -> RatTestAlgebraElement

def WeilGramMatrix
    (functional : FullWeilFunctional)
    (ruler : FiniteWeilRuler)
    (i j : Nat) : Rat :=
  functional.value
    (WeilBilinearArgument
      (ruler.testAt i).test
      (ruler.testAt j).test)

def SymmetricMatrix
    (size : Nat) (entry : Nat -> Nat -> Rat) : Prop :=
  ∀ i j : Nat, i < size -> j < size ->
    RatEq (entry i j) (entry j i)

structure RationalPrincipalMinorPSDCertificate
    (size : Nat) (entry : Nat -> Nat -> Rat) where
  principalMinorValue : List Nat -> Rat
  diagonal_minor_readback :
    ∀ i : Nat, i < size ->
      RatEq (principalMinorValue [i]) (entry i i)
  pair_minor_readback :
    ∀ i j : Nat, i < size -> j < size ->
      RatEq
        (principalMinorValue [i, j])
        (ratSub
          (ratMul (entry i i) (entry j j))
          (ratMul (entry i j) (entry j i)))
  principal_minor_nonnegative :
    ∀ indices : List Nat,
      indices.length ≤ size ->
        (∀ i : Nat, i ∈ indices -> i < size) ->
        ratLe ratZero (principalMinorValue indices)

def PSD : Nat -> (Nat -> Nat -> Rat) -> Prop
  | 0, _entry => True
  | 1, entry => ratLe ratZero (entry 0 0)
  | 2, entry =>
      ratLe ratZero (entry 0 0) ∧
        ratLe ratZero (entry 1 1) ∧
          ratLe
            (ratMul (entry 0 1) (entry 1 0))
            (ratMul (entry 0 0) (entry 1 1))
  | Nat.succ (Nat.succ (Nat.succ m)), entry =>
      ∃ cert :
        RationalPrincipalMinorPSDCertificate
          (Nat.succ (Nat.succ (Nat.succ m))) entry,
        ∀ indices : List Nat,
          indices.length ≤ Nat.succ (Nat.succ (Nat.succ m)) ->
            (∀ i : Nat, i ∈ indices ->
              i < Nat.succ (Nat.succ (Nat.succ m))) ->
            ratLe ratZero (cert.principalMinorValue indices)

def unitWeilFunctional : FullWeilFunctional where
  value := fun _h => ratOne
  explicit_formula_obligations :=
    [ WeilExplicitFormulaObligation.primePowerDistributionMatchesVonMangoldt,
      WeilExplicitFormulaObligation.archimedeanGammaKernelMatchesXi,
      WeilExplicitFormulaObligation.polePairNormalizationMatchesCompletedZeta ]
  limit_obligations :=
    [ WeilLimitObligation.truncationsConvergeToFullDistribution,
      WeilLimitObligation.ratTestAlgebraSeparatesOffLineReflections,
      WeilLimitObligation.finiteEnclosuresRespectLocatedRealLimit ]

def unitWeilRuler : FiniteWeilRuler where
  size := 2
  testAt := fun _i => originRatTestAlgebraElement

theorem unitWeilGram_symmetric :
    SymmetricMatrix
      unitWeilRuler.size
      (WeilGramMatrix unitWeilFunctional unitWeilRuler) := by
  intro i j _hi _hj
  change RatEq ratOne ratOne
  exact RatEq_refl ratOne

theorem weilGram_psd_witness :
    PSD
      unitWeilRuler.size
      (WeilGramMatrix unitWeilFunctional unitWeilRuler) := by
  change
    ratLe ratZero ratOne ∧
      ratLe ratZero ratOne ∧
        ratLe (ratMul ratOne ratOne) (ratMul ratOne ratOne)
  exact ⟨ratOne_nonneg, ⟨ratOne_nonneg, ratLe_refl (ratMul ratOne ratOne)⟩⟩

def singletonRuler (g : RatTestAlgebraElement) : FiniteWeilRuler where
  size := 1
  testAt := fun _i => g

def AllFiniteWeilGramPSD (functional : FullWeilFunctional) : Prop :=
  ∀ ruler : FiniteWeilRuler,
    PSD ruler.size (WeilGramMatrix functional ruler)

theorem singleton_weil_gram_psd_to_global_weil_positivity
    (functional : FullWeilFunctional)
    (allGramPSD : AllFiniteWeilGramPSD functional) :
    GlobalWeilPositivity functional := by
  intro g
  have hsingleton :
      PSD
        (singletonRuler g).size
        (WeilGramMatrix functional (singletonRuler g)) :=
    allGramPSD (singletonRuler g)
  change ratLe ratZero (functional.value g.test.quadraticArgument)
  exact hsingleton

structure WeilGramReduction where
  functional : FullWeilFunctional
  all_finite_gram_psd : AllFiniteWeilGramPSD functional

theorem global_weil_positivity_via_finite_gram_psd
    (reduction : WeilGramReduction) :
    GlobalWeilPositivity reduction.functional :=
  singleton_weil_gram_psd_to_global_weil_positivity
    reduction.functional reduction.all_finite_gram_psd

theorem rh_via_finite_weil_gram_psd
    (positivityReduction : WeilPositivityReduction)
    (gramReduction : WeilGramReduction)
    (sameFunctional :
      gramReduction.functional = positivityReduction.functional) :
    ConstructiveRH := by
  have positivity :
      GlobalWeilPositivity positivityReduction.functional := by
    rw [← sameFunctional]
    exact global_weil_positivity_via_finite_gram_psd gramReduction
  exact rh_via_weil_positivity positivityReduction
    positivity

end BEDC.Derived.RHRoute.WeilGramRoute
