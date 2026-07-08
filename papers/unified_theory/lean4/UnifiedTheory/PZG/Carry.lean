import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.List.Basic

namespace UnifiedTheory

/--
Zeckendorf 进位重写单步(Fibonacci 指标列上):合并相邻、拆双。
保 `Σ fib`,是 theorem 5.7 算法归一化的基础关系。
-/
inductive CarryStep : List ℕ → List ℕ → Prop where
  | merge (p q : List ℕ) (i : ℕ) :
      CarryStep (p ++ i :: (i + 1) :: q) (p ++ (i + 2) :: q)
  | double (p q : List ℕ) (i : ℕ) :
      CarryStep (p ++ (i + 2) :: (i + 2) :: q) (p ++ (i + 3) :: i :: q)

/-- A Zeckendorf carry step preserves the sum of Fibonacci values. -/
theorem CarryStep.value_preserving {l l' : List ℕ} (h : CarryStep l l') :
    (l.map Nat.fib).sum = (l'.map Nat.fib).sum := by
  cases h with
  | merge p q i =>
      simp [Nat.fib_add_two, Nat.add_comm, Nat.add_left_comm]
  | double p q i =>
      have h3 : Nat.fib (i + 3) = Nat.fib (i + 1) + Nat.fib (i + 2) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := i + 1))
      have h2 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
      simp [h2, h3, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end UnifiedTheory
