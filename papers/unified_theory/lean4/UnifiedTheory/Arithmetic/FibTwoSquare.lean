import Mathlib.Data.Nat.Fib.Zeckendorf

namespace UnifiedTheory

theorem fib_odd_isZeckendorf_atom (k : ℕ) : List.IsZeckendorfRep [2 * k + 3] := by
  simp [List.IsZeckendorfRep]

theorem fib_odd_primitive_twoSquare (k : ℕ) :
    ∃ a b : ℕ, a.Coprime b ∧ Nat.fib (2 * k + 3) = a ^ 2 + b ^ 2 := by
  refine ⟨Nat.fib (k + 2), Nat.fib (k + 1), ?_, ?_⟩
  · exact (Nat.fib_coprime_fib_succ (k + 1)).symm
  · have h := Nat.fib_two_mul_add_one (k + 1)
    simpa [
      show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
      show (k + 1) + 1 = k + 2 by omega
    ] using h

/-- **本原二平方 Zeckendorf 原子**:奇 Fibonacci `fib(2k+3)` 既是单符号 Zeckendorf 表 `[2k+3]`,
又是本原二平方 `fib(k+2)²+fib(k+1)²`(相邻 Fibonacci 互素)。给出无穷可验"原子"核对象族。 -/
theorem fib_odd_atom (k : ℕ) :
    List.IsZeckendorfRep [2 * k + 3] ∧
      ∃ a b : ℕ, a.Coprime b ∧ Nat.fib (2 * k + 3) = a ^ 2 + b ^ 2 :=
  ⟨fib_odd_isZeckendorf_atom k, fib_odd_primitive_twoSquare k⟩

end UnifiedTheory
