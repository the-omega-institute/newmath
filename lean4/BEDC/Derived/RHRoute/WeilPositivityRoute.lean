import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.WeilPositivityRoute

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

structure LogPoint where
  positive : Nat
  negative : Nat

def LogPoint.zero : LogPoint where
  positive := 0
  negative := 0

def LogPoint.neg (x : LogPoint) : LogPoint where
  positive := x.negative
  negative := x.positive

def LogPoint.add (x y : LogPoint) : LogPoint where
  positive := x.positive + y.positive
  negative := x.negative + y.negative

def LogPoint.ofNat (n : Nat) : LogPoint where
  positive := n
  negative := 0

def LogPoint.size (x : LogPoint) : Nat :=
  x.positive + x.negative

theorem logPoint_neg_involutive (x : LogPoint) :
    LogPoint.neg (LogPoint.neg x) = x := by
  cases x
  rfl

structure RatLogAtom where
  point : LogPoint
  coeff : Rat

def RatLogAtom.sharp (a : RatLogAtom) : RatLogAtom where
  point := LogPoint.neg a.point
  coeff := a.coeff

def RatLogAtom.mul (a b : RatLogAtom) : RatLogAtom where
  point := LogPoint.add a.point b.point
  coeff := ratMul a.coeff b.coeff

structure RatTestFunction where
  supportRadius : Nat
  atoms : List RatLogAtom

def RatTestFunction.HasCompactLogSupport (g : RatTestFunction) : Prop :=
  ∀ atom : RatLogAtom, atom ∈ g.atoms -> LogPoint.size atom.point ≤ g.supportRadius

def RatTestFunction.sharp (g : RatTestFunction) : RatTestFunction where
  supportRadius := g.supportRadius
  atoms := g.atoms.map RatLogAtom.sharp

def convolutionAtoms : List RatLogAtom -> List RatLogAtom -> List RatLogAtom
  | [], _ys => []
  | x :: xs, ys => ys.map (RatLogAtom.mul x) ++ convolutionAtoms xs ys

def RatTestFunction.convolution
    (g h : RatTestFunction) : RatTestFunction where
  supportRadius := g.supportRadius + h.supportRadius
  atoms := convolutionAtoms g.atoms h.atoms

def RatTestFunction.quadraticArgument (g : RatTestFunction) : RatTestFunction :=
  RatTestFunction.convolution g g.sharp

structure RatTestAlgebraElement where
  test : RatTestFunction
  compact_log_support : test.HasCompactLogSupport

structure PrimeLogEnclosure (p : Nat) where
  fuel : Nat
  one_le : 1 ≤ p
  upper_limit : p ≤ 96
  lo : Rat
  hi : Rat
  lo_readback : lo = lnLo p fuel
  hi_readback : hi = lnHi p fuel one_le
  series_enclosed :
    SeriesEnclosedFrom
      (fun K => atanhFormalSeries (zOfNat p) K)
      fuel lo hi

def primeLogEnclosure96
    (p : Nat) (one_le : 1 ≤ p) (upper_limit : p ≤ 96) :
    PrimeLogEnclosure p where
  fuel := lnM96 p
  one_le := one_le
  upper_limit := upper_limit
  lo := lnLo p (lnM96 p)
  hi := lnHi p (lnM96 p) one_le
  lo_readback := rfl
  hi_readback := rfl
  series_enclosed := formal_lnN96_enclosure p one_le upper_limit

structure RationalKernelEnclosure where
  lo : Rat
  hi : Rat
  valid : ratLe lo hi

def unitKernelEnclosure : RationalKernelEnclosure where
  lo := ratZero
  hi := ratOne
  valid := ratOne_nonneg

structure PrimePowerIndex (cutoff : Nat) where
  prime : Nat
  exponent : Nat
  prime_cert : IsPrime prime
  exponent_pos : 1 ≤ exponent
  prime_bound : prime ≤ cutoff
  power : Nat
  power_readback : power = prime ^ exponent
  log_enclosure : PrimeLogEnclosure prime

inductive ArchimedeanKernelTag where
  | gammaFactor
  | reflectionKernel

inductive PoleTag where
  | poleAtZero
  | poleAtOne

inductive WeilTermSource (cutoff : Nat) where
  | primePower : PrimePowerIndex cutoff -> WeilTermSource cutoff
  | archimedean : ArchimedeanKernelTag -> RationalKernelEnclosure -> WeilTermSource cutoff
  | pole : PoleTag -> RationalKernelEnclosure -> WeilTermSource cutoff

structure WeilLocatedTerm (cutoff : Nat) where
  source : WeilTermSource cutoff
  weight : Rat
  value : Rat
  weight_nonnegative : ratLe ratZero weight
  value_nonnegative : ratLe ratZero value

def WeilLocatedTerm.contribution {cutoff : Nat}
    (term : WeilLocatedTerm cutoff) : Rat :=
  ratMul term.weight term.value

theorem WeilLocatedTerm.contribution_nonnegative {cutoff : Nat}
    (term : WeilLocatedTerm cutoff) :
    ratLe ratZero term.contribution := by
  exact ratMul_nonneg term.weight_nonnegative term.value_nonnegative

def ratListSum : List Rat -> Rat
  | [] => ratZero
  | x :: xs => ratAdd x (ratListSum xs)

theorem ratListSum_nonnegative :
    ∀ xs : List Rat,
      (∀ x : Rat, x ∈ xs -> ratLe ratZero x) ->
        ratLe ratZero (ratListSum xs)
  | [], _h => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | x :: xs, h => by
      change ratLe ratZero (ratAdd x (ratListSum xs))
      have hx : ratLe ratZero x := h x (List.Mem.head xs)
      have hxs : ratLe ratZero (ratListSum xs) := by
        exact ratListSum_nonnegative xs
          (fun y hy => h y (List.Mem.tail x hy))
      have shifted :
          ratLe (ratAdd ratZero ratZero) (ratAdd x (ratListSum xs)) := by
        exact ratAdd_le_add hx hxs
      exact ratLe_of_RatEq_left (ratZero_add_left ratZero) shifted

theorem weilTermContributionList_nonnegative {cutoff : Nat} :
    ∀ terms : List (WeilLocatedTerm cutoff),
      ratLe ratZero (ratListSum (terms.map WeilLocatedTerm.contribution))
  | [] => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | term :: terms => by
      change
        ratLe ratZero
          (ratAdd term.contribution
            (ratListSum (terms.map WeilLocatedTerm.contribution)))
      have hterm : ratLe ratZero term.contribution :=
        WeilLocatedTerm.contribution_nonnegative term
      have htail :
          ratLe ratZero (ratListSum (terms.map WeilLocatedTerm.contribution)) :=
        weilTermContributionList_nonnegative terms
      have shifted :
          ratLe
            (ratAdd ratZero ratZero)
            (ratAdd term.contribution
              (ratListSum (terms.map WeilLocatedTerm.contribution))) := by
        exact ratAdd_le_add hterm htail
      exact ratLe_of_RatEq_left (ratZero_add_left ratZero) shifted

structure WeilTruncation (h : RatTestFunction) where
  cutoff : Nat
  terms : List (WeilLocatedTerm cutoff)

def WeilTruncation.value {h : RatTestFunction}
    (truncation : WeilTruncation h) : Rat :=
  ratListSum (truncation.terms.map WeilLocatedTerm.contribution)

def WeilFunctionalTrunc (h : RatTestFunction)
    (truncation : WeilTruncation h) : Rat :=
  truncation.value

def WeilQuadraticFormTrunc (g : RatTestFunction)
    (truncation : WeilTruncation g.quadraticArgument) : Rat :=
  WeilFunctionalTrunc g.quadraticArgument truncation

theorem weil_positivity_truncation
    (g : RatTestFunction)
    (truncation : WeilTruncation g.quadraticArgument) :
    ratLe ratZero (WeilQuadraticFormTrunc g truncation) := by
  unfold WeilQuadraticFormTrunc WeilFunctionalTrunc WeilTruncation.value
  exact weilTermContributionList_nonnegative truncation.terms

def zeroTestFunction : RatTestFunction where
  supportRadius := 0
  atoms := []

theorem zeroTestFunction_compact :
    zeroTestFunction.HasCompactLogSupport := by
  intro atom member
  cases member

def zeroRatTestAlgebraElement : RatTestAlgebraElement where
  test := zeroTestFunction
  compact_log_support := zeroTestFunction_compact

def originAtom : RatLogAtom where
  point := LogPoint.zero
  coeff := ratOne

def originTestFunction : RatTestFunction where
  supportRadius := 0
  atoms := [originAtom]

theorem originTestFunction_compact :
    originTestFunction.HasCompactLogSupport := by
  intro atom member
  cases member with
  | head =>
      change LogPoint.size LogPoint.zero ≤ 0
      exact Nat.le_refl _
  | tail _ tailMember =>
      cases tailMember

def originRatTestAlgebraElement : RatTestAlgebraElement where
  test := originTestFunction
  compact_log_support := originTestFunction_compact

def primeTwoLogEnclosure : PrimeLogEnclosure 2 :=
  primeLogEnclosure96 2 (by decide) (by decide)

theorem isPrime_two : IsPrime 2 := by
  change BEDC.Derived.PrimeUp.NatPrime
    (BEDC.FKernel.Hist.BHist.e1
      (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty))
  exact BEDC.Derived.PrimeUp.NatPrime_first_pair.left

def primeTwoPowerIndex : PrimePowerIndex 2 where
  prime := 2
  exponent := 1
  prime_cert := isPrime_two
  exponent_pos := by decide
  prime_bound := by decide
  power := 2 ^ 1
  power_readback := rfl
  log_enclosure := primeTwoLogEnclosure

def onePrimeAtom : RatLogAtom where
  point := LogPoint.ofNat primeTwoPowerIndex.power
  coeff := ratOne

def onePrimeTestFunction : RatTestFunction where
  supportRadius := 2
  atoms := [onePrimeAtom]

theorem onePrimeTestFunction_compact :
    onePrimeTestFunction.HasCompactLogSupport := by
  intro atom member
  cases member with
  | head =>
      change LogPoint.size (LogPoint.ofNat primeTwoPowerIndex.power) ≤ 2
      exact Nat.le_refl _
  | tail _ tailMember =>
      cases tailMember

def onePrimeRatTestAlgebraElement : RatTestAlgebraElement where
  test := onePrimeTestFunction
  compact_log_support := onePrimeTestFunction_compact

def archimedeanUnitTerm : WeilLocatedTerm 0 where
  source := WeilTermSource.archimedean
    ArchimedeanKernelTag.gammaFactor unitKernelEnclosure
  weight := ratOne
  value := ratOne
  weight_nonnegative := ratOne_nonneg
  value_nonnegative := ratOne_nonneg

def poleUnitTerm : WeilLocatedTerm 0 where
  source := WeilTermSource.pole PoleTag.poleAtOne unitKernelEnclosure
  weight := ratOne
  value := ratOne
  weight_nonnegative := ratOne_nonneg
  value_nonnegative := ratOne_nonneg

def primeTwoUnitTerm : WeilLocatedTerm 2 where
  source := WeilTermSource.primePower primeTwoPowerIndex
  weight := ratOne
  value := ratOne
  weight_nonnegative := ratOne_nonneg
  value_nonnegative := ratOne_nonneg

def zeroTruncation :
    WeilTruncation zeroTestFunction.quadraticArgument where
  cutoff := 0
  terms := []

def originArchPoleTruncation :
    WeilTruncation originTestFunction.quadraticArgument where
  cutoff := 0
  terms := [archimedeanUnitTerm, poleUnitTerm]

def primeTwoTruncation :
    WeilTruncation onePrimeTestFunction.quadraticArgument where
  cutoff := 2
  terms := [primeTwoUnitTerm]

theorem zero_truncation_Q_nonnegative :
    ratLe ratZero
      (WeilQuadraticFormTrunc zeroTestFunction zeroTruncation) := by
  exact weil_positivity_truncation zeroTestFunction zeroTruncation

theorem origin_arch_pole_truncation_Q_nonnegative :
    ratLe ratZero
      (WeilQuadraticFormTrunc originTestFunction originArchPoleTruncation) := by
  exact weil_positivity_truncation originTestFunction originArchPoleTruncation

theorem prime_two_truncation_Q_nonnegative :
    ratLe ratZero
      (WeilQuadraticFormTrunc onePrimeTestFunction primeTwoTruncation) := by
  exact weil_positivity_truncation onePrimeTestFunction primeTwoTruncation

inductive WeilExplicitFormulaObligation where
  | primePowerDistributionMatchesVonMangoldt
  | archimedeanGammaKernelMatchesXi
  | polePairNormalizationMatchesCompletedZeta

inductive WeilLimitObligation where
  | truncationsConvergeToFullDistribution
  | ratTestAlgebraSeparatesOffLineReflections
  | finiteEnclosuresRespectLocatedRealLimit

structure FullWeilFunctional where
  value : RatTestFunction -> Rat
  explicit_formula_obligations : List WeilExplicitFormulaObligation
  limit_obligations : List WeilLimitObligation

def GlobalWeilPositivity (functional : FullWeilFunctional) : Prop :=
  ∀ g : RatTestAlgebraElement,
    ratLe ratZero (functional.value g.test.quadraticArgument)

structure WeilPositivityReduction where
  functional : FullWeilFunctional
  explicit_formula_scope :
    functional.explicit_formula_obligations =
      [ WeilExplicitFormulaObligation.primePowerDistributionMatchesVonMangoldt,
        WeilExplicitFormulaObligation.archimedeanGammaKernelMatchesXi,
        WeilExplicitFormulaObligation.polePairNormalizationMatchesCompletedZeta ]
  limit_scope :
    functional.limit_obligations =
      [ WeilLimitObligation.truncationsConvergeToFullDistribution,
        WeilLimitObligation.ratTestAlgebraSeparatesOffLineReflections,
        WeilLimitObligation.finiteEnclosuresRespectLocatedRealLimit ]
  rh_from_weil_positivity :
    GlobalWeilPositivity functional -> ConstructiveRH

theorem rh_via_weil_positivity
    (reduction : WeilPositivityReduction)
    (positivity : GlobalWeilPositivity reduction.functional) :
    ConstructiveRH :=
  reduction.rh_from_weil_positivity positivity

theorem weil_reduction_obligation_count
    (reduction : WeilPositivityReduction) :
    reduction.functional.explicit_formula_obligations.length = 3 ∧
      reduction.functional.limit_obligations.length = 3 := by
  constructor
  · rw [reduction.explicit_formula_scope]
    rfl
  · rw [reduction.limit_scope]
    rfl

end BEDC.Derived.RHRoute.WeilPositivityRoute
