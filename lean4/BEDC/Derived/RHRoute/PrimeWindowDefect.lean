import BEDC.Derived.RHRoute.FinitePrimeWindow
import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.PrimeWindowDefect

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.RHRoute.ConstructiveRHStatement

abbrev PrimeWindow :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

abbrev IsPrime :=
  BEDC.Derived.RHRoute.FinitePrimeWindow.IsPrime

abbrev Rat :=
  RatNum

abbrev RatComplex :=
  ConstructiveRHStatement.RatComplex

abbrev NontrivialZetaZero :=
  ConstructiveRHStatement.NontrivialZetaZero

abbrev OnCriticalLine :=
  ConstructiveRHStatement.OnCriticalLine

abbrev ConstructiveRH :=
  ConstructiveRHStatement.ConstructiveRH

structure WeightedPrimeWindow where
  window : PrimeWindow
  weight : Nat -> Rat
  weight_apart : ∀ p : Nat, window.mem p -> ratApart0 (weight p)

structure StripOffsetPoint where
  delta : Rat
  tau : Rat

def OffHalf (pt : StripOffsetPoint) : Prop :=
  ratApart0 pt.delta

def primeWindowDefectAt
    (W : WeightedPrimeWindow) (pt : StripOffsetPoint)
    (p : Nat) (_hp : W.window.mem p) : Rat :=
  ratMul pt.delta (W.weight p)

def PrimeWindowDefectWitness
    (W : WeightedPrimeWindow) (pt : StripOffsetPoint) : Prop :=
  ∃ p : Nat, ∃ hp : W.window.mem p,
    ratApart0 (primeWindowDefectAt W pt p hp)

theorem offHalf_to_primeWindowDefectWitness
    (W : WeightedPrimeWindow) (pt : StripOffsetPoint)
    (p : Nat) (hp : W.window.mem p) (hδ : ratApart0 pt.delta) :
    PrimeWindowDefectWitness W pt := by
  exact ⟨p, hp, ratMul_apart0 hδ (W.weight_apart p hp)⟩

theorem two_isPrime : IsPrime 2 := by
  change BEDC.Derived.PrimeUp.NatPrime
    (BEDC.Derived.IntUp.natToUnary 2)
  exact BEDC.Derived.PrimeUp.NatPrime_first_pair.left

def canonicalWindow : PrimeWindow where
  elems := [2]
  nodup :=
    BEDC.Derived.RHRoute.FinitePrimeWindow.NoDup.cons
      (by
        intro member
        cases member)
      BEDC.Derived.RHRoute.FinitePrimeWindow.NoDup.nil
  all_prime :=
    BEDC.Derived.RHRoute.FinitePrimeWindow.All.cons
      two_isPrime
      BEDC.Derived.RHRoute.FinitePrimeWindow.All.nil

theorem canonical_two_mem : canonicalWindow.mem 2 := by
  exact List.Mem.head []

theorem ratOne_apart0 : ratApart0 ratOne :=
  ratOne_apart

def canonicalWeighted : WeightedPrimeWindow where
  window := canonicalWindow
  weight := fun _ => ratOne
  weight_apart := by
    intro _p _hp
    exact ratOne_apart0

def canonicalOffHalfPoint : StripOffsetPoint where
  delta := ratOne
  tau := ratZero

theorem canonicalPrimeWindowDefectWitness :
    PrimeWindowDefectWitness canonicalWeighted canonicalOffHalfPoint :=
  offHalf_to_primeWindowDefectWitness
    canonicalWeighted canonicalOffHalfPoint 2 canonical_two_mem ratOne_apart0

def OffsetReadsZero (s : RatComplex) (pt : StripOffsetPoint) : Prop :=
  RatEq pt.delta
    (ratSub s.re BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat)

def PrimeWindowDefectZeroIncompatibility : Prop :=
  ∀ s : RatComplex, NontrivialZetaZero s ->
    (∃ W : WeightedPrimeWindow, ∃ pt : StripOffsetPoint,
      PrimeWindowDefectWitness W pt ∧ OffsetReadsZero s pt) ->
      False

def FiniteWindowGlobalCollapse : Prop :=
  ∀ s : RatComplex, NontrivialZetaZero s ->
    (∀ pt : StripOffsetPoint, OffsetReadsZero s pt -> Not (OffHalf pt)) ->
      OnCriticalLine s

structure PrimeWindowRHObligations where
  o1_carrier_closure : Prop
  o3_defect_formula : Prop
  o4_defect_zero_incompatibility : PrimeWindowDefectZeroIncompatibility
  o5_located_collapse : FiniteWindowGlobalCollapse

theorem obligations_imply_constructiveRH
    (O : PrimeWindowRHObligations) :
    ConstructiveRH := by
  intro s hs
  apply O.o5_located_collapse s hs
  intro pt reads offHalf
  have defect : PrimeWindowDefectWitness canonicalWeighted pt :=
    offHalf_to_primeWindowDefectWitness
      canonicalWeighted pt 2 canonical_two_mem offHalf
  exact O.o4_defect_zero_incompatibility s hs
    ⟨canonicalWeighted, pt, And.intro defect reads⟩

end BEDC.Derived.RHRoute.PrimeWindowDefect
