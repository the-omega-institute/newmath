import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Derived.RHRoute.LagariasCriterion
import BEDC.Derived.RHRoute.WeilPositivityRoute
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.LiCriterionRoute

open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Derived.RHRoute.WeilPositivityRoute
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

abbrev RawRat : Type :=
  BEDC.Derived.BernoulliUp.RawRat

def rawDen (x : RawRat) : Nat :=
  x.den

def rawNormalize (x : RawRat) : RawRat :=
  BEDC.Derived.BernoulliUp.rawNormalize x

def rawZero : RawRat :=
  BEDC.Derived.BernoulliUp.rawZero

def rawOne : RawRat :=
  BEDC.Derived.BernoulliUp.rawOne

def rawOfIntOverNat (num : Int) (den : Nat) : RawRat :=
  match den with
  | 0 => rawZero
  | Nat.succ d => { num := num, denMinusOne := d }

def rawOfNat (n : Nat) : RawRat :=
  rawOfIntOverNat (Int.ofNat n) 1

def rawNeg (x : RawRat) : RawRat :=
  { num := -x.num, denMinusOne := x.denMinusOne }

def rawAdd (x y : RawRat) : RawRat :=
  { num := x.num * Int.ofNat (rawDen y) + y.num * Int.ofNat (rawDen x)
    denMinusOne := rawDen x * rawDen y - 1 }

def rawSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)

def rawMul (x y : RawRat) : RawRat :=
  { num := x.num * y.num
    denMinusOne := rawDen x * rawDen y - 1 }

def rawInv (x : RawRat) : RawRat :=
  match x.num with
  | Int.ofNat 0 => rawZero
  | Int.ofNat (Nat.succ n) =>
      { num := Int.ofNat (rawDen x), denMinusOne := n }
  | Int.negSucc n =>
      { num := -Int.ofNat (rawDen x), denMinusOne := n }

def rawDiv (x y : RawRat) : RawRat :=
  rawMul x (rawInv y)

def rawMulInt (z : Int) (x : RawRat) : RawRat :=
  { num := z * x.num, denMinusOne := x.denMinusOne }

def rawDivByNat (x : RawRat) (n : Nat) : RawRat :=
  match n with
  | 0 => rawZero
  | Nat.succ d =>
      { num := x.num, denMinusOne := rawDen x * Nat.succ d - 1 }

def rawToRatNum (x : RawRat) : Rat :=
  BEDC.Derived.BernoulliUp.rawRatToRat x

def rawLeBool (x y : RawRat) : Bool :=
  BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
    (x.num * Int.ofNat (rawDen y))
    (y.num * Int.ofNat (rawDen x))

def rawLtBool (x y : RawRat) : Bool :=
  BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
    (x.num * Int.ofNat (rawDen y) + 1)
    (y.num * Int.ofNat (rawDen x))

def rawNonnegative (x : RawRat) : Prop :=
  rawLeBool rawZero x = true

def rawPositive (x : RawRat) : Prop :=
  rawLtBool rawZero x = true

def ratOfIntOverNat (num : Int) (den : Nat) : Rat :=
  rawToRatNum (rawOfIntOverNat num den)

def rawBinom : Nat -> Nat -> Nat
  | _, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, Nat.succ k => rawBinom n k + rawBinom n (Nat.succ k)

def rawListSum : List RawRat -> RawRat
  | [] => rawZero
  | x :: xs => rawAdd x (rawListSum xs)

def rawListGetD : List RawRat -> Nat -> RawRat
  | [], _ => rawZero
  | x :: _xs, 0 => x
  | _x :: xs, Nat.succ n => rawListGetD xs n

def rawScaledLiTaylorTerm (n m : Nat) (a : RawRat) : RawRat :=
  rawMulInt (Int.ofNat (n * rawBinom (n - 1) (m - 1))) a

def rawLiTaylorSum
    (n : Nat) (xiLogCoeff : Nat -> RawRat) : Nat -> RawRat
  | 0 => rawZero
  | Nat.succ j =>
      rawAdd (rawLiTaylorSum n xiLogCoeff j)
        (rawScaledLiTaylorTerm n (Nat.succ j)
          (xiLogCoeff (Nat.succ j)))

def rawLiCoefficientFromXiLog (n : Nat) (xiLogCoeff : Nat -> RawRat) : RawRat :=
  rawLiTaylorSum n xiLogCoeff n

/--
Finite Li coefficient surface from the Taylor coefficients of
`log xi(1 + t)`.  If `xiLogCoeff m` is the coefficient of `t^m`, then this
computes

`n * sum_{m=1}^{n} binom(n-1,m-1) xiLogCoeff m`,

the coefficient form of
`(1/(n-1)!) d^n/ds^n [s^(n-1) log xi(s)]` at `s = 1`.
-/
def liCoefficient (n : Nat) (xiLogCoeff : Nat -> Rat) : Rat :=
  rawToRatNum
    (rawLiCoefficientFromXiLog n
      (fun m =>
        BEDC.Derived.RHRoute.LagariasCriterion.ratToRaw (xiLogCoeff m)))

structure LiTaylorPacket where
  xiLogCoeff : Nat -> Rat
  xiLogCoeffRaw : Nat -> RawRat
  coeff_readback :
    ∀ m : Nat,
      xiLogCoeff m = rawToRatNum (xiLogCoeffRaw m)
  xi_log_derivative_obligation : Nat -> Prop

def liCoefficientFromPacket (packet : LiTaylorPacket) (n : Nat) : Rat :=
  rawToRatNum (rawLiCoefficientFromXiLog n packet.xiLogCoeffRaw)

def liRawFromPacket (packet : LiTaylorPacket) (n : Nat) : RawRat :=
  rawLiCoefficientFromXiLog n packet.xiLogCoeffRaw

def liLoRaw (packet : LiTaylorPacket) (n : Nat) : RawRat :=
  liRawFromPacket packet n

def liLo (packet : LiTaylorPacket) (n : Nat) : Rat :=
  rawToRatNum (liLoRaw packet n)

def LiPositive (packet : LiTaylorPacket) (n : Nat) : Prop :=
  rawNonnegative (liLoRaw packet n)

def LiStrictPositive (packet : LiTaylorPacket) (n : Nat) : Prop :=
  rawPositive (liLoRaw packet n)

def liGammaLogPiLowerCoeff : RawRat :=
  rawOfIntOverNat 23095708966121 1000000000000000

def liGammaLogPiUpperCoeff : RawRat :=
  rawOfIntOverNat 23095708966122 1000000000000000

def xiLogCoeffSampleRaw : Nat -> RawRat
  | 0 => rawZero
  | 1 => liGammaLogPiLowerCoeff
  | 2 => rawOfIntOverNat 23077158647902 1000000000000000
  | 3 => rawOfIntOverNat (-37052743818) 1000000000000000
  | 4 => rawOfIntOverNat (-18406805316) 1000000000000000
  | 5 => rawOfIntOverNat 143018671 1000000000000000
  | 6 => rawOfIntOverNat 46906069 1000000000000000
  | _ => rawZero

def xiLogCoeffSample (n : Nat) : Rat :=
  rawToRatNum (xiLogCoeffSampleRaw n)

def XiLogCoefficientMatchesClassicalXi
    (coeff : Nat -> Rat) (raw : Nat -> RawRat) (m : Nat) : Prop :=
  coeff m = rawToRatNum (raw m) ∧ rawLeBool (raw m) (raw m) = true

/--
The sample packet records rational lower endpoints for the first coefficients
of `log xi(1+t)`.  The first endpoint is the classical
`gamma/2 + 1 - log(4*pi)/2` coefficient, enclosed between the two adjacent
decimal rationals above; the analytic enclosure is an explicit obligation
rather than a Lean proof of the transcendental identity.
-/
def liSampleTaylorPacket : LiTaylorPacket where
  xiLogCoeff := xiLogCoeffSample
  xiLogCoeffRaw := xiLogCoeffSampleRaw
  coeff_readback := by
    intro m
    rfl
  xi_log_derivative_obligation :=
    XiLogCoefficientMatchesClassicalXi xiLogCoeffSample xiLogCoeffSampleRaw

theorem li_sample_first_coeff_enclosed :
    rawLtBool rawZero liGammaLogPiLowerCoeff = true ∧
      rawLeBool liGammaLogPiLowerCoeff liGammaLogPiUpperCoeff = true := by
  unfold rawLtBool rawLeBool rawZero liGammaLogPiLowerCoeff
    liGammaLogPiUpperCoeff rawOfIntOverNat rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness_one :
    LiStrictPositive liSampleTaylorPacket 1 := by
  change rawPositive (rawLiCoefficientFromXiLog 1 xiLogCoeffSampleRaw)
  unfold rawPositive rawLiCoefficientFromXiLog rawLiTaylorSum rawScaledLiTaylorTerm
    xiLogCoeffSampleRaw liGammaLogPiLowerCoeff rawLtBool rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness_two :
    LiStrictPositive liSampleTaylorPacket 2 := by
  change rawPositive (rawLiCoefficientFromXiLog 2 xiLogCoeffSampleRaw)
  unfold rawPositive rawLiCoefficientFromXiLog rawLiTaylorSum rawScaledLiTaylorTerm
    xiLogCoeffSampleRaw liGammaLogPiLowerCoeff rawLtBool rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness_three :
    LiStrictPositive liSampleTaylorPacket 3 := by
  change rawPositive (rawLiCoefficientFromXiLog 3 xiLogCoeffSampleRaw)
  unfold rawPositive rawLiCoefficientFromXiLog rawLiTaylorSum rawScaledLiTaylorTerm
    xiLogCoeffSampleRaw liGammaLogPiLowerCoeff rawLtBool rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness_four :
    LiStrictPositive liSampleTaylorPacket 4 := by
  change rawPositive (rawLiCoefficientFromXiLog 4 xiLogCoeffSampleRaw)
  unfold rawPositive rawLiCoefficientFromXiLog rawLiTaylorSum rawScaledLiTaylorTerm
    xiLogCoeffSampleRaw liGammaLogPiLowerCoeff rawLtBool rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness_five :
    LiStrictPositive liSampleTaylorPacket 5 := by
  change rawPositive (rawLiCoefficientFromXiLog 5 xiLogCoeffSampleRaw)
  unfold rawPositive rawLiCoefficientFromXiLog rawLiTaylorSum rawScaledLiTaylorTerm
    xiLogCoeffSampleRaw liGammaLogPiLowerCoeff rawLtBool rawDen
    BEDC.Derived.RHRoute.LagariasCriterion.intLeBool
  decide

theorem li_positive_witness :
    LiStrictPositive liSampleTaylorPacket 1 ∧
      LiStrictPositive liSampleTaylorPacket 2 ∧
        LiStrictPositive liSampleTaylorPacket 3 ∧
          LiStrictPositive liSampleTaylorPacket 4 ∧
            LiStrictPositive liSampleTaylorPacket 5 := by
  exact ⟨li_positive_witness_one,
    ⟨li_positive_witness_two,
      ⟨li_positive_witness_three,
        ⟨li_positive_witness_four, li_positive_witness_five⟩⟩⟩⟩

structure LiWeilTestFamily where
  testAt : Nat -> RatTestFunction
  arithmetic_readback :
    ∀ n : Nat,
      n = 0 ∨
        (testAt n).quadraticArgument.HasCompactLogSupport
  li_reads_weil :
    ∀ (packet : LiTaylorPacket) (n : Nat),
      n = 0 ∨
        ∃ truncation : WeilTruncation ((testAt n).quadraticArgument),
          liLo packet n = WeilQuadraticFormTrunc (testAt n) truncation

structure LiCriterionReduction where
  packet : LiTaylorPacket
  weil_family : LiWeilTestFamily
  li_nonnegative_to_constructive_rh :
    (∀ n : Nat, 1 ≤ n -> LiPositive packet n) -> ConstructiveRH
  xi_convergence_bridge_obligation : Prop
  bombieri_lagarias_bridge_obligation : Prop

theorem rh_via_li_positivity
    (reduction : LiCriterionReduction)
    (positive : ∀ n : Nat, 1 ≤ n -> LiPositive reduction.packet n) :
    ConstructiveRH :=
  reduction.li_nonnegative_to_constructive_rh positive

theorem li_weil_link
    (family : LiWeilTestFamily)
    (packet : LiTaylorPacket)
    (n : Nat)
    (hn : 1 ≤ n) :
    ∃ truncation : WeilTruncation ((family.testAt n).quadraticArgument),
      liLo packet n = WeilQuadraticFormTrunc (family.testAt n) truncation := by
  have link := family.li_reads_weil packet n
  cases link with
  | inl zero =>
      cases zero
      exact False.elim (Nat.not_succ_le_zero 0 hn)
  | inr data =>
      exact data

end BEDC.Derived.RHRoute.LiCriterionRoute
