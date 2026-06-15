namespace BEDC.Derived.Window6Fibonacci

def fib : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

structure WindowStateCount where
  total : Nat
  zeroLast : Nat

def step : WindowStateCount -> WindowStateCount
  | ⟨total, zeroLast⟩ => ⟨total + zeroLast, total⟩

def stateCount : Nat -> WindowStateCount
  | 0 => ⟨1, 1⟩
  | n + 1 => step (stateCount n)

def stableCount (m : Nat) : Nat :=
  (stateCount m).total

def zeroTerminalCount (m : Nat) : Nat :=
  (stateCount m).zeroLast

theorem stateCount_eq_fib_pair (m : Nat) :
    stateCount m = ⟨fib (m + 2), fib (m + 1)⟩ := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      rw [stateCount, ih]
      rfl

theorem stableWordCount_eq_fib (m : Nat) :
    stableCount m = fib (m + 2) := by
  unfold stableCount
  rw [stateCount_eq_fib_pair]

theorem zeroTerminalCount_eq_fib (m : Nat) :
    zeroTerminalCount m = fib (m + 1) := by
  unfold zeroTerminalCount
  rw [stateCount_eq_fib_pair]

theorem stableCount_zero : stableCount 0 = 1 := by
  rfl

theorem stableCount_one : stableCount 1 = 2 := by
  rfl

theorem stableCount_two : stableCount 2 = 3 := by
  rfl

theorem stableCount_six : stableCount 6 = 21 := by
  rfl

theorem fib_eight : fib 8 = 21 := by
  rfl

theorem stableCount_six_eq_fib_eight : stableCount 6 = fib 8 := by
  rfl

end BEDC.Derived.Window6Fibonacci
