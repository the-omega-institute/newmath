import BEDC.Derived.BeattyUp

namespace BEDC.Derived.WythoffUp

open BEDC.Derived.BeattyUp
open BEDC.Derived.ZeckendorfUp

/-!
Wythoff 行在这里通过 `BeattyUp` 已有的 Fibonacci 比值表面导出。
本文件只使用 Nat/List 数据, 不假设实数 floor 运算。
-/

def positiveBeatty (r : NatRatio) (n : Nat) : Nat :=
  (n * r.numerator) / r.denominator

def wythoffRatioApprox (k : Nat) : NatRatio :=
  goldenRatioApprox k

def wythoffLowerApprox (k n : Nat) : Nat :=
  positiveBeatty (wythoffRatioApprox k) n

def wythoffUpperApprox (k n : Nat) : Nat :=
  wythoffLowerApprox k n + n

def wythoffLowerPrefix (k count : Nat) : List Nat :=
  (positivePrefix count).map (wythoffLowerApprox k)

def wythoffUpperPrefix (k count : Nat) : List Nat :=
  (positivePrefix count).map (wythoffUpperApprox k)

def wythoffLowerZeckendorf (k n : Nat) : List Nat :=
  zeckendorf (wythoffLowerApprox k n)

def wythoffUpperZeckendorf (k n : Nat) : List Nat :=
  zeckendorf (wythoffUpperApprox k n)

theorem positiveBeatty_eq_rationalBeatty_succ (r : NatRatio) (n : Nat) :
    positiveBeatty r (n + 1) = rationalBeatty r n := by
  rfl

theorem wythoffLowerApprox_eq_goldenBeattyApprox_succ (k n : Nat) :
    wythoffLowerApprox k (n + 1) = goldenBeattyApprox k n := by
  rfl

theorem wythoffUpperApprox_eq_lower_add (k n : Nat) :
    wythoffUpperApprox k n = wythoffLowerApprox k n + n := by
  rfl

theorem wythoffLowerZeckendorf_restore (k n : Nat) :
    zeckendorfValue (wythoffLowerZeckendorf k n) =
      wythoffLowerApprox k n := by
  exact zeckendorf_sum_restore (wythoffLowerApprox k n)

theorem wythoffUpperZeckendorf_restore (k n : Nat) :
    zeckendorfValue (wythoffUpperZeckendorf k n) =
      wythoffUpperApprox k n := by
  exact zeckendorf_sum_restore (wythoffUpperApprox k n)

theorem wythoffUpperZeckendorf_value_eq_lower_add (k n : Nat) :
    zeckendorfValue (wythoffUpperZeckendorf k n) =
      wythoffLowerApprox k n + n := by
  rw [wythoffUpperZeckendorf_restore]
  rfl

def wythoffArrayRowFrom (x y : Nat) : Nat -> List Nat
  | 0 => []
  | fuel + 1 => x :: wythoffArrayRowFrom y (x + y) fuel

def wythoffArrayRow (k n fuel : Nat) : List Nat :=
  wythoffArrayRowFrom (wythoffLowerApprox k n) (wythoffUpperApprox k n) fuel

theorem wythoffArrayRow_zero (k n : Nat) :
    wythoffArrayRow k n 0 = [] := by
  rfl

theorem wythoffArrayRow_one (k n : Nat) :
    wythoffArrayRow k n 1 = [wythoffLowerApprox k n] := by
  rfl

theorem wythoffArrayRow_two (k n : Nat) :
    wythoffArrayRow k n 2 =
      [wythoffLowerApprox k n, wythoffUpperApprox k n] := by
  rfl

theorem wythoffArrayRow_three (k n : Nat) :
    wythoffArrayRow k n 3 =
      [wythoffLowerApprox k n, wythoffUpperApprox k n,
        wythoffLowerApprox k n + wythoffUpperApprox k n] := by
  rfl

theorem wythoffArrayRow_seed_gap (k n : Nat) :
    wythoffArrayRow k n 2 =
      [wythoffLowerApprox k n, wythoffLowerApprox k n + n] := by
  rw [wythoffArrayRow_two]
  rfl

inductive ZeckendorfTerminalSide where
  | lower
  | upper
deriving DecidableEq, Repr

def flipTerminalSide : ZeckendorfTerminalSide -> ZeckendorfTerminalSide
  | ZeckendorfTerminalSide.lower => ZeckendorfTerminalSide.upper
  | ZeckendorfTerminalSide.upper => ZeckendorfTerminalSide.lower

def indexTerminalSide : Nat -> ZeckendorfTerminalSide
  | 0 => ZeckendorfTerminalSide.lower
  | 1 => ZeckendorfTerminalSide.upper
  | n + 2 => indexTerminalSide n

def terminalSideFromListAux : ZeckendorfTerminalSide -> List Nat -> ZeckendorfTerminalSide
  | side, [] => side
  | _, index :: rest => terminalSideFromListAux (indexTerminalSide index) rest

def terminalSideFromList (fallback : ZeckendorfTerminalSide)
    (indices : List Nat) : ZeckendorfTerminalSide :=
  terminalSideFromListAux fallback indices

def wythoffZeckendorfSide (n : Nat) : ZeckendorfTerminalSide :=
  terminalSideFromList ZeckendorfTerminalSide.lower (zeckendorf n)

def WythoffLowerZeckendorfClass (n : Nat) : Prop :=
  wythoffZeckendorfSide n = ZeckendorfTerminalSide.lower

def WythoffUpperZeckendorfClass (n : Nat) : Prop :=
  wythoffZeckendorfSide n = ZeckendorfTerminalSide.upper

theorem wythoffZeckendorf_positive_partition (n : Nat) :
    (WythoffLowerZeckendorfClass (n + 1) ->
        WythoffUpperZeckendorfClass (n + 1) -> False) ∧
      (WythoffLowerZeckendorfClass (n + 1) ∨
        WythoffUpperZeckendorfClass (n + 1)) := by
  constructor
  · intro lower upper
    unfold WythoffLowerZeckendorfClass at lower
    unfold WythoffUpperZeckendorfClass at upper
    cases hside : wythoffZeckendorfSide (n + 1) with
    | lower =>
        exact ZeckendorfTerminalSide.noConfusion (Eq.trans hside.symm upper)
    | upper =>
        exact ZeckendorfTerminalSide.noConfusion (Eq.trans hside.symm lower)
  · cases hside : wythoffZeckendorfSide (n + 1) with
    | lower =>
        exact Or.inl hside
    | upper =>
        exact Or.inr hside

def wythoffFibonacciWindowLower : List Nat :=
  wythoffLowerPrefix 5 9

def wythoffFibonacciWindowUpper : List Nat :=
  wythoffUpperPrefix 5 6

theorem wythoffFibonacciWindowLower_values :
    wythoffFibonacciWindowLower = [1, 3, 4, 6, 8, 9, 11, 12, 14] := by
  decide

theorem wythoffFibonacciWindowUpper_values :
    wythoffFibonacciWindowUpper = [2, 5, 7, 10, 13, 15] := by
  decide

theorem wythoffFibonacciWindowPartition :
    listDisjoint wythoffFibonacciWindowLower wythoffFibonacciWindowUpper = true ∧
      sortedMerge wythoffFibonacciWindowLower wythoffFibonacciWindowUpper =
        positivePrefix 15 := by
  decide

theorem wythoffFibonacciWindowLower_terminal_side :
    wythoffFibonacciWindowLower.map wythoffZeckendorfSide =
      [ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.lower] := by
  rfl

theorem wythoffFibonacciWindowUpper_terminal_side :
    wythoffFibonacciWindowUpper.map wythoffZeckendorfSide =
      [ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.upper,
        ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.upper,
        ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.upper] := by
  rfl

theorem wythoffPositiveWindow_terminal_side_partition :
    (positivePrefix 15).map wythoffZeckendorfSide =
      [ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.upper,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.upper,
        ZeckendorfTerminalSide.lower, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.upper, ZeckendorfTerminalSide.lower,
        ZeckendorfTerminalSide.upper] := by
  rfl

end BEDC.Derived.WythoffUp
