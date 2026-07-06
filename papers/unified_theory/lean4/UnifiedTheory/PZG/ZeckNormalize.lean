import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Multiset.Basic

namespace UnifiedTheory

/--
Complete Zeckendorf carry-normalization rewriting on multisets.
The zero-drop and `1 -> 2` rules make the normal forms exactly Zeckendorf sets.
This is the computational normalization core for theorem 5.7.
-/
inductive CarryFull : Multiset ℕ → Multiset ℕ → Prop where
  | zero (Γ : Multiset ℕ) : CarryFull (0 ::ₘ Γ) Γ
  | one (Γ : Multiset ℕ) : CarryFull (1 ::ₘ Γ) (2 ::ₘ Γ)
  | merge (Γ : Multiset ℕ) (i : ℕ) :
      CarryFull (i ::ₘ (i + 1) ::ₘ Γ) ((i + 2) ::ₘ Γ)
  | double (Γ : Multiset ℕ) (i : ℕ) :
      CarryFull ((i + 2) ::ₘ (i + 2) ::ₘ Γ) ((i + 3) ::ₘ i ::ₘ Γ)

/-- Fibonacci value of a multiset of Zeckendorf indices. -/
def fibVal (M : Multiset ℕ) : ℕ := (M.map Nat.fib).sum

private lemma fib_double (i : ℕ) :
    Nat.fib (i + 2) + Nat.fib (i + 2) = Nat.fib (i + 3) + Nat.fib i := by
  have h2 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
  have h3 : Nat.fib (i + 3) = Nat.fib (i + 1) + Nat.fib (i + 2) := by
    simpa [Nat.add_assoc] using (Nat.fib_add_two (n := i + 1))
  rw [h2, h3]
  omega

/-- Every complete carry-normalization step preserves Fibonacci value. -/
theorem CarryFull.fibVal_preserving {M N : Multiset ℕ} (h : CarryFull M N) :
    fibVal M = fibVal N := by
  cases h with
  | zero Γ =>
      simp [fibVal]
  | one Γ =>
      simp [fibVal]
  | merge Γ i =>
      simp [fibVal, Nat.fib_add_two, Nat.add_comm, Nat.add_left_comm]
  | double Γ i =>
      simp [fibVal, fib_double, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Index weight used as a strictly decreasing termination measure. -/
def ixWt : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 5
  | 3 => 8
  | 4 => 9
  | (n + 5) => 2 * (n + 5) + 1

/-- Multiset potential for complete carry-normalization. -/
def μ (M : Multiset ℕ) : ℕ := (M.map ixWt).sum

private lemma ixWt_four_add (n : ℕ) : ixWt (n + 4) = 2 * (n + 4) + 1 := by
  cases n with
  | zero =>
      simp [ixWt]
  | succ n =>
      simp [ixWt, Nat.add_assoc]

private lemma ixWt_merge_lt (i : ℕ) : ixWt (i + 2) < ixWt i + ixWt (i + 1) := by
  match i with
  | 0 =>
      simp [ixWt]
  | 1 =>
      simp [ixWt]
  | 2 =>
      simp [ixWt]
  | 3 =>
      simp [ixWt]
  | n + 4 =>
      rw [ixWt_four_add n, ixWt_four_add (n + 1), ixWt_four_add (n + 2)]
      omega

private lemma ixWt_double_lt (i : ℕ) :
    ixWt (i + 3) + ixWt i < ixWt (i + 2) + ixWt (i + 2) := by
  match i with
  | 0 =>
      simp [ixWt]
  | 1 =>
      simp [ixWt]
  | 2 =>
      simp [ixWt]
  | 3 =>
      simp [ixWt]
  | n + 4 =>
      rw [ixWt_four_add n, ixWt_four_add (n + 2), ixWt_four_add (n + 3)]
      omega

/-- Every complete carry-normalization step strictly lowers the potential `μ`. -/
theorem CarryFull.μ_step_lt {M N : Multiset ℕ} (h : CarryFull M N) : μ N < μ M := by
  cases h with
  | zero Γ =>
      simp [μ, ixWt]
  | one Γ =>
      simp [μ, ixWt]
  | merge Γ i =>
      simp only [μ, Multiset.map_cons, Multiset.sum_cons]
      simpa [Nat.add_assoc] using
        Nat.add_lt_add_right (ixWt_merge_lt i) (Multiset.map ixWt Γ).sum
  | double Γ i =>
      simp only [μ, Multiset.map_cons, Multiset.sum_cons]
      simpa [Nat.add_assoc] using
        Nat.add_lt_add_right (ixWt_double_lt i) (Multiset.map ixWt Γ).sum

/-- Complete carry-normalization is terminating. -/
theorem CarryFull.terminates : WellFounded (fun N M => CarryFull M N) :=
  Subrelation.wf (fun {_N _M} h => CarryFull.μ_step_lt h) (InvImage.wf μ Nat.lt_wfRel.wf)

end UnifiedTheory
