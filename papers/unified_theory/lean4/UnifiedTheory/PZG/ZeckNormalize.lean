import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Logic.Relation

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

/-- A multiset is normal when no complete carry rule can fire from it. -/
def Normal (M : Multiset ℕ) : Prop := ∀ N, ¬ CarryFull M N

/-- Zeckendorf multisets contain distinct non-adjacent indices, all at least two. -/
def IsZeckMS (M : Multiset ℕ) : Prop :=
  M.Nodup ∧ (∀ i ∈ M, 2 ≤ i) ∧ (∀ i ∈ M, i + 1 ∉ M)

lemma normal_no_zero {M : Multiset ℕ} (h : Normal M) : 0 ∉ M := by
  intro h0
  have hM : 0 ::ₘ M.erase 0 = M := Multiset.cons_erase h0
  exact h _ (by simpa [hM] using CarryFull.zero (M.erase 0))

lemma normal_no_one {M : Multiset ℕ} (h : Normal M) : 1 ∉ M := by
  intro h1
  have hM : 1 ::ₘ M.erase 1 = M := Multiset.cons_erase h1
  exact h _ (by simpa [hM] using CarryFull.one (M.erase 1))

lemma normal_count_le_one {M : Multiset ℕ} (hM : Normal M) : ∀ i, M.count i ≤ 1 := by
  intro k
  by_contra hk
  have hk2 : 2 ≤ M.count k := by omega
  match k with
  | 0 =>
      have hmem : 0 ∈ M := Multiset.count_pos.mp (by omega)
      exact (normal_no_zero hM) hmem
  | 1 =>
      have hmem : 1 ∈ M := Multiset.count_pos.mp (by omega)
      exact (normal_no_one hM) hmem
  | i + 2 =>
      have hmem₁ : i + 2 ∈ M := Multiset.count_pos.mp (by omega)
      have hmem₂ : i + 2 ∈ M.erase (i + 2) := by
        apply Multiset.count_pos.mp
        rw [Multiset.count_erase_self]
        omega
      have h₁ : (i + 2) ::ₘ M.erase (i + 2) = M := Multiset.cons_erase hmem₁
      have h₂ :
          (i + 2) ::ₘ (M.erase (i + 2)).erase (i + 2) = M.erase (i + 2) :=
        Multiset.cons_erase hmem₂
      let Γ := (M.erase (i + 2)).erase (i + 2)
      have hsrc : (i + 2) ::ₘ (i + 2) ::ₘ Γ = M := by
        unfold Γ
        rw [h₂, h₁]
      exact hM _ (by simpa [hsrc] using CarryFull.double Γ i)

lemma normal_no_adjacent {M : Multiset ℕ} (hM : Normal M) :
    ∀ i, i ∈ M → i + 1 ∉ M := by
  intro i hi hj
  have hne : i + 1 ≠ i := by omega
  have hmem : i + 1 ∈ M.erase i := (Multiset.mem_erase_of_ne hne).mpr hj
  have h₁ : i ::ₘ M.erase i = M := Multiset.cons_erase hi
  have h₂ : (i + 1) ::ₘ (M.erase i).erase (i + 1) = M.erase i :=
    Multiset.cons_erase hmem
  let Γ := (M.erase i).erase (i + 1)
  have hsrc : i ::ₘ (i + 1) ::ₘ Γ = M := by
    unfold Γ
    rw [h₂, h₁]
  exact hM _ (by simpa [hsrc] using CarryFull.merge Γ i)

theorem normal_isZeckMS {M : Multiset ℕ} (h : Normal M) : IsZeckMS M := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Multiset.nodup_iff_count_le_one]
    exact normal_count_le_one h
  · intro i hi
    match i with
    | 0 => exact absurd hi (normal_no_zero h)
    | 1 => exact absurd hi (normal_no_one h)
    | _ + 2 => omega
  · exact normal_no_adjacent h

/-- The descending list associated to a multiset of Zeckendorf indices. -/
def zList (M : Multiset ℕ) : List ℕ := M.sort (fun a b : ℕ => b ≤ a)

private lemma zList_nodup {M : Multiset ℕ} (hM : M.Nodup) : (zList M).Nodup := by
  rw [← Multiset.coe_nodup, zList, Multiset.sort_eq]
  exact hM

private lemma zList_mem {M : Multiset ℕ} {i : ℕ} : i ∈ zList M ↔ i ∈ M := by
  rw [zList, Multiset.mem_sort]

private lemma zList_pairwise_gap {M : Multiset ℕ} (hM : IsZeckMS M) :
    (zList M).Pairwise (fun a b : ℕ => b + 2 ≤ a) := by
  have hsort : (zList M).Pairwise (fun a b : ℕ => b ≤ a) := by
    unfold zList
    exact Multiset.pairwise_sort M (fun a b : ℕ => b ≤ a)
  have hnodup : (zList M).Nodup := zList_nodup hM.1
  have hstrict : (zList M).Pairwise (fun a b : ℕ => b < a) := by
    have hge : (zList M).SortedGE := by
      simpa [List.sortedGE_iff_pairwise] using hsort
    have hgt : (zList M).SortedGT := hge.sortedGT_of_nodup hnodup
    simpa [List.sortedGT_iff_pairwise] using hgt
  exact hstrict.imp_of_mem (l := zList M) (fun {a b} ha hb hlt => by
    have haM : a ∈ M := zList_mem.mp ha
    have hbM : b ∈ M := zList_mem.mp hb
    have hnot : b + 1 ≠ a := by
      intro h
      exact hM.2.2 b hbM (h ▸ haM)
    omega)

/-- The descending list of a normal multiset is a Zeckendorf representation. -/
theorem normal_zList_isZeckendorfRep {M : Multiset ℕ} (hM : Normal M) :
    (zList M).IsZeckendorfRep := by
  have hz := normal_isZeckMS hM
  unfold List.IsZeckendorfRep
  rw [List.isChain_append]
  refine ⟨(zList_pairwise_gap hz).isChain, List.isChain_singleton 0, ?_⟩
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst y
  have hxM : x ∈ M := zList_mem.mp (List.mem_of_mem_getLast? hx)
  exact hz.2.1 x hxM

private lemma zList_sum_fib_eq_fibVal (M : Multiset ℕ) :
    ((zList M).map Nat.fib).sum = fibVal M := by
  have hsort : (↑(zList M) : Multiset ℕ) = M := by
    unfold zList
    exact Multiset.sort_eq M (fun a b : ℕ => b ≤ a)
  rw [fibVal, ← Multiset.sum_coe, ← Multiset.map_coe, hsort]

/-- Normal Zeckendorf multisets with the same Fibonacci value have the same descending list. -/
theorem normal_unique_of_same_value {M N : Multiset ℕ}
    (hM : Normal M) (hN : Normal N) (hv : fibVal M = fibVal N) :
    zList M = zList N := by
  have hMz := normal_zList_isZeckendorfRep hM
  have hNz := normal_zList_isZeckendorfRep hN
  have hsM : ((zList M).map Nat.fib).sum = fibVal M := zList_sum_fib_eq_fibVal M
  have hsN : ((zList N).map Nat.fib).sum = fibVal N := zList_sum_fib_eq_fibVal N
  have hsum : ((zList M).map Nat.fib).sum = ((zList N).map Nat.fib).sum := by
    rw [hsM, hsN, hv]
  calc
    zList M = (((zList M).map Nat.fib).sum).zeckendorf := by
      exact (Nat.zeckendorf_sum_fib hMz).symm
    _ = (((zList N).map Nat.fib).sum).zeckendorf := by
      rw [hsum]
    _ = zList N := Nat.zeckendorf_sum_fib hNz

/-- Reflexive-transitive complete carry reduction. -/
def Reduces : Multiset ℕ → Multiset ℕ → Prop := Relation.ReflTransGen CarryFull

/-- Complete carry reduction preserves Fibonacci value. -/
theorem fibVal_reduces {M N : Multiset ℕ} (h : Reduces M N) : fibVal M = fibVal N := by
  induction h with
  | refl => rfl
  | tail hrt hstep ih =>
      exact ih.trans (CarryFull.fibVal_preserving hstep)

/-- Every multiset has a complete carry-normal form. -/
theorem exists_normal (M : Multiset ℕ) : ∃ N, Reduces M N ∧ Normal N :=
  (CarryFull.terminates).induction (C := fun M => ∃ N, Reduces M N ∧ Normal N) M (fun M ih => by
    by_cases hM : Normal M
    · exact ⟨M, Relation.ReflTransGen.refl, hM⟩
    · rw [Normal] at hM
      push_neg at hM
      obtain ⟨N, hMN⟩ := hM
      obtain ⟨N', hN'red, hN'norm⟩ := ih N hMN
      exact ⟨N', Relation.ReflTransGen.head hMN hN'red, hN'norm⟩)

/--
Complete carry rewriting is strongly normalizing: every multiset reduces to a
unique normal form, value is preserved along reduction, and confluence follows
from Zeckendorf uniqueness rather than a critical-pair analysis.
-/
theorem normal_form_unique {M N₁ N₂ : Multiset ℕ}
    (h₁ : Reduces M N₁) (hn₁ : Normal N₁)
    (h₂ : Reduces M N₂) (hn₂ : Normal N₂) : N₁ = N₂ := by
  have hv : fibVal N₁ = fibVal N₂ := by
    rw [← fibVal_reduces h₁, ← fibVal_reduces h₂]
  have hz : zList N₁ = zList N₂ := normal_unique_of_same_value hn₁ hn₂ hv
  have e₁ : (↑(zList N₁) : Multiset ℕ) = N₁ := by
    unfold zList
    exact Multiset.sort_eq N₁ (fun a b : ℕ => b ≤ a)
  have e₂ : (↑(zList N₂) : Multiset ℕ) = N₂ := by
    unfold zList
    exact Multiset.sort_eq N₂ (fun a b : ℕ => b ≤ a)
  rw [← e₁, ← e₂, hz]

/-- A complete carry-normal form is the Zeckendorf representative of `fibVal M`. -/
theorem normal_form_is_zeckendorf (M : Multiset ℕ) :
    ∃ N, Reduces M N ∧ Normal N ∧ fibVal N = fibVal M := by
  obtain ⟨N, hred, hnorm⟩ := exists_normal M
  exact ⟨N, hred, hnorm, (fibVal_reduces hred).symm⟩

end UnifiedTheory
