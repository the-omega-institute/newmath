import BEDC.Derived.NonCollapseInvariantUp
import BEDC.Derived.RationalUp
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.BoxStreamSqrt2Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.NonCollapseInvariantUp
open BEDC.Derived.RHRoute.ZetaBoxEvaluator

abbrev natTwo : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

theorem natTwo_unary : UnaryHistory natTwo := by
  exact unary_e1_closed (unary_e1_closed unary_empty)

theorem natTwo_prime : NatPrime natTwo := by
  exact NatPrime_first_pair.left

def intTwo : IntegerUp :=
  intOfNat natTwo natTwo_unary

def ratTwo : RatNum :=
  intToRat intTwo

def sqrt2Low : RatNum :=
  ratOne

def sqrt2High : RatNum :=
  ratTwo

theorem ratOne_le_ratTwo : ratLe sqrt2Low sqrt2High := by
  unfold sqrt2Low sqrt2High ratTwo intTwo ratOne ratLe intLe
  apply BEDC.Derived.IntUp.pairLe_of_length_order
  · exact intToPair_carrier _
  · exact intToPair_carrier _
  decide

def sqrt2ReInterval : QInterval :=
  { lo := sqrt2Low
    hi := sqrt2High
    valid := ratOne_le_ratTwo }

def zeroInterval : QInterval :=
  { lo := ratZero
    hi := ratZero
    valid := ratLe_refl ratZero }

def sqrt2Box : ComplexBox :=
  { re := sqrt2ReInterval
    im := zeroInterval }

def sqrt2BoxGauge : BoxGauge :=
  { fits := fun box _k => box = sqrt2Box
    fits_weaken := by
      intro box hi lo _hlo hfit
      exact hfit }

def sqrt2BoxStream : BoxStream sqrt2BoxGauge :=
  { box := fun _k => sqrt2Box
    modulus := fun k => k
    modulus_mono := by
      intro i j hij
      exact hij
    fits_at := by
      intro k n hn
      change sqrt2Box = sqrt2Box
      rfl }

theorem sqrt2BoxStream_boxAt_fits (k : Nat) :
    sqrt2BoxGauge.fits (boxAt sqrt2BoxStream k) k :=
  boxAt_fits sqrt2BoxStream k

theorem sqrt2BoxStream_explicit_modulus (k : Nat) :
    sqrt2BoxStream.modulus k = k := by
  rfl

theorem sqrt2BoxStream_boxAt_eq (k : Nat) :
    boxAt sqrt2BoxStream k = sqrt2Box := by
  rfl

structure Sqrt2BoxStreamCandidate where
  gauge : BoxGauge
  point : BoxStream gauge
  base_lower : RatNum
  base_upper : RatNum
  base_lower_le_upper : ratLe base_lower base_upper
  modulus_identity : ∀ k : Nat, point.modulus k = k
  box_at : ∀ k : Nat, boxAt point k = sqrt2Box

def sqrt2BoxStreamCandidate : Sqrt2BoxStreamCandidate :=
  { gauge := sqrt2BoxGauge
    point := sqrt2BoxStream
    base_lower := sqrt2Low
    base_upper := sqrt2High
    base_lower_le_upper := ratOne_le_ratTwo
    modulus_identity := sqrt2BoxStream_explicit_modulus
    box_at := sqrt2BoxStream_boxAt_eq }

def sqrt2ApartnessBridgeToWitness
    (apart : ∀ q : RatNum, BoxStreamApart sqrt2BoxGauge sqrt2BoxStream q) :
    BoxStreamNonCollapseWitness :=
  { gauge := sqrt2BoxGauge
    point := sqrt2BoxStream
    invariant := apart }

theorem sqrt2_candidate_has_boxstream_surface :
    sqrt2BoxStreamCandidate.gauge = sqrt2BoxGauge ∧
      sqrt2BoxStreamCandidate.point = sqrt2BoxStream := by
  constructor <;> rfl

end BEDC.Derived.BoxStreamSqrt2Up
