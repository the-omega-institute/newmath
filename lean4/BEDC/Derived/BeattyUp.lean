import BEDC.Derived.FibonacciUp
import BEDC.Derived.GoldenMeanShiftUp
import BEDC.Derived.ZeckendorfUp

namespace BEDC.Derived.BeattyUp

structure NatRatio where
  numerator : Nat
  denominator : Nat
deriving DecidableEq, Repr

def rationalBeatty (r : NatRatio) (n : Nat) : Nat :=
  ((n + 1) * r.numerator) / r.denominator

def rayleighCompanion (r : NatRatio) : NatRatio :=
  { numerator := r.numerator, denominator := r.numerator - r.denominator }

def shiftedComplementBeatty (r : NatRatio) (n : Nat) : Nat :=
  (((n + 1) * r.numerator) - 1) / (r.numerator - r.denominator)

def positivePrefix (fuel : Nat) : List Nat :=
  (List.range fuel).map (fun n => n + 1)

def rationalBeattyPrefix (r : NatRatio) (count : Nat) : List Nat :=
  (List.range count).map (rationalBeatty r)

def shiftedComplementPrefix (r : NatRatio) (count : Nat) : List Nat :=
  (List.range count).map (shiftedComplementBeatty r)

def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLeBool a b

def sortedMergeFuel : Nat -> List Nat -> List Nat -> List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      match natLeBool x y with
      | true => x :: sortedMergeFuel fuel xs (y :: ys)
      | false => y :: sortedMergeFuel fuel (x :: xs) ys

def sortedMerge (xs ys : List Nat) : List Nat :=
  sortedMergeFuel (xs.length + ys.length) xs ys

def listDisjoint : List Nat -> List Nat -> Bool
  | [], _ => true
  | x :: xs, ys =>
      if ys.contains x then
        false
      else
        listDisjoint xs ys

def fiveTwoRayleigh : NatRatio :=
  { numerator := 5, denominator := 2 }

def fiveTwoBeattyPrefix : List Nat :=
  rationalBeattyPrefix fiveTwoRayleigh 6

def fiveTwoComplementPrefix : List Nat :=
  shiftedComplementPrefix fiveTwoRayleigh 9

theorem fiveTwoRayleigh_reciprocal_numerators :
    fiveTwoRayleigh.denominator +
        (rayleighCompanion fiveTwoRayleigh).denominator =
      fiveTwoRayleigh.numerator := by
  rfl

theorem rationalBeatty_five_two_values :
    fiveTwoBeattyPrefix = [2, 5, 7, 10, 12, 15] := by
  decide

theorem shiftedComplement_five_two_values :
    fiveTwoComplementPrefix = [1, 3, 4, 6, 8, 9, 11, 13, 14] := by
  decide

theorem rationalRayleighComplementPartition :
    listDisjoint fiveTwoBeattyPrefix fiveTwoComplementPrefix = true ∧
      sortedMerge fiveTwoBeattyPrefix fiveTwoComplementPrefix = positivePrefix 15 := by
  decide

def goldenRatioApprox (k : Nat) : NatRatio :=
  { numerator := BEDC.Derived.FibonacciUp.fib (k + 3),
    denominator := BEDC.Derived.FibonacciUp.fib (k + 2) }

def goldenBeattyApprox (k n : Nat) : Nat :=
  rationalBeatty (goldenRatioApprox k) n

def goldenBeattyZeckendorf (k n : Nat) : List Nat :=
  BEDC.Derived.ZeckendorfUp.zeckendorf (goldenBeattyApprox k n)

theorem goldenBeattyZeckendorfRestore (k n : Nat) :
    BEDC.Derived.ZeckendorfUp.zeckendorfValue
        (goldenBeattyZeckendorf k n) =
      goldenBeattyApprox k n := by
  exact BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore
    (goldenBeattyApprox k n)

theorem goldenRatioApprox_goldenKernel_row (k : Nat) :
    BEDC.Derived.Window6Transfer.npow
        BEDC.Derived.GoldenMeanShiftUp.goldenKernel (k + 2) =
      ⟨(((goldenRatioApprox k).numerator : Nat) : Int),
        (((goldenRatioApprox k).denominator : Nat) : Int),
        (((goldenRatioApprox k).denominator : Nat) : Int),
        ((BEDC.Derived.FibonacciUp.fib (k + 1) : Nat) : Int)⟩ := by
  exact BEDC.Derived.GoldenMeanShiftUp.goldenKernel_transfer_power_fib (k + 1)

theorem goldenBeattyApprox_first_window :
    (List.range 8).map (goldenBeattyApprox 4) =
      [1, 3, 4, 6, 8, 9, 11, 13] := by
  decide

end BEDC.Derived.BeattyUp
