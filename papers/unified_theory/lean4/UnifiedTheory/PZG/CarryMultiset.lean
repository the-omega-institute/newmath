import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Multiset.Basic

namespace UnifiedTheory

/--
多重集版进位重写(序无关):合并 `{i,i+1} → {i+2}`、加倍
`{i+2,i+2} → {i+3,i}`。

序无关使临界对 `{i,i+1,i+2}` 两路归约都到 `{i,i+3}`,可 join,这是
theorem 5.7 唯一标准形之正确基础。
-/
inductive CarryStepM : Multiset ℕ → Multiset ℕ → Prop where
  | merge (rest : Multiset ℕ) (i : ℕ) :
      CarryStepM (i ::ₘ (i + 1) ::ₘ rest) ((i + 2) ::ₘ rest)
  | double (rest : Multiset ℕ) (i : ℕ) :
      CarryStepM ((i + 2) ::ₘ (i + 2) ::ₘ rest) ((i + 3) ::ₘ i ::ₘ rest)

/-- A multiset carry step preserves the sum of Fibonacci values. -/
theorem CarryStepM.value_preserving {m m' : Multiset ℕ} (h : CarryStepM m m') :
    (m.map Nat.fib).sum = (m'.map Nat.fib).sum := by
  cases h with
  | merge rest i =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      simp [Nat.fib_add_two, Nat.add_comm, Nat.add_left_comm]
  | double rest i =>
      have h3 : Nat.fib (i + 3) = Nat.fib (i + 1) + Nat.fib (i + 2) := by
        simpa [Nat.add_assoc] using (Nat.fib_add_two (n := i + 1))
      have h2 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
      simp only [Multiset.map_cons, Multiset.sum_cons]
      simp [h2, h3, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end UnifiedTheory
