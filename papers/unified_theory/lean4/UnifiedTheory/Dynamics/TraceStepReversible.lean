import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace UnifiedTheory

variable {R : Type*} [CommRing R]

/-- Fibonacci-Markov 迹映射 `(a,b,c) ↦ (b,c,bc-a)`。 -/
def TraceStep (v : R × R × R) : R × R × R :=
  (v.2.1, v.2.2, v.2.1 * v.2.2 - v.1)

/-- Fibonacci-Markov 迹映射的逆 `(a,b,c) ↦ (ab-c,a,b)`。 -/
def TraceStepInv (v : R × R × R) : R × R × R :=
  (v.1 * v.2.1 - v.2.2, v.1, v.2.1)

/-- Fibonacci-Markov 迹映射 `(a,b,c) ↦ (b,c,bc-a)` 的左逆；
迹动力学无信息丢失。 -/
theorem traceStepInv_leftInverse :
    Function.LeftInverse (TraceStepInv (R := R)) TraceStep := by
  rintro ⟨a, b, c⟩
  simp [TraceStep, TraceStepInv]

/-- Fibonacci-Markov 迹映射 `(a,b,c) ↦ (b,c,bc-a)` 的右逆；
逆映射为 `(a,b,c) ↦ (ab-c,a,b)`。 -/
theorem traceStepInv_rightInverse :
    Function.RightInverse (TraceStepInv (R := R)) TraceStep := by
  rintro ⟨a, b, c⟩
  simp [TraceStep, TraceStepInv]

/-- Fibonacci-Markov 迹步进给出 `R × R × R` 上的等价。 -/
def TraceStepEquiv : (R × R × R) ≃ (R × R × R) where
  toFun := TraceStep
  invFun := TraceStepInv
  left_inv := traceStepInv_leftInverse
  right_inv := traceStepInv_rightInverse

theorem traceStep_injective : Function.Injective (TraceStep (R := R)) :=
  (TraceStepEquiv (R := R)).injective

private theorem finite_injective_pure_periodic {α : Type*} [Fintype α] {f : α → α}
    (hf : Function.Injective f) (x : α) :
    ∃ k : ℕ, 0 < k ∧ f^[k] x = x := by
  let N := Fintype.card α
  let orbit : Fin (N + 1) → α := fun j => (f^[j.val]) x
  have hcard : (Finset.univ : Finset α).card <
      (Finset.univ : Finset (Fin (N + 1))).card := by
    simp [N]
  obtain ⟨a, _ha, b, _hb, hne, hab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin (N + 1))))
      (t := (Finset.univ : Finset α))
      hcard
      (f := orbit)
      (by intro y _hy; exact Finset.mem_univ (orbit y))
  have close_of_lt :
      ∀ {i j : Fin (N + 1)}, i.val < j.val →
        (f^[i.val]) x = (f^[j.val]) x →
        ∃ k : ℕ, 0 < k ∧ f^[k] x = x := by
    intro i j hij hij_eq
    let k := j.val - i.val
    have hkpos : 0 < k := Nat.sub_pos_of_lt hij
    have hsum : i.val + k = j.val := by
      dsimp [k]
      exact Nat.add_sub_of_le (Nat.le_of_lt hij)
    have hrewrite : (f^[j.val]) x = (f^[i.val]) ((f^[k]) x) := by
      calc
        (f^[j.val]) x = (f^[i.val + k]) x := by rw [hsum]
        _ = (f^[i.val]) ((f^[k]) x) := Function.iterate_add_apply f i.val k x
    have hcancel : (f^[i.val]) ((f^[k]) x) = (f^[i.val]) x := by
      rw [← hrewrite]
      exact hij_eq.symm
    have hinj_iter : Function.Injective (f^[i.val]) :=
      Function.Injective.iterate hf i.val
    exact ⟨k, hkpos, hinj_iter hcancel⟩
  have hval_ne : a.val ≠ b.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · exact close_of_lt (i := a) (j := b) hlt (by simpa [orbit] using hab)
  · exact close_of_lt (i := b) (j := a) hgt (by simpa [orbit] using hab.symm)

/-- 模每个 `q`，迹动力学纯周期：无前周期尾、无状态合并，每个状态已在环上。
这是可逆性与有限鸽巢原理的组合，排除有限模迹动力学中的 preperiodic tail。 -/
theorem traceStep_zmod_pure_periodic (q : ℕ) [NeZero q]
    (v : ZMod q × ZMod q × ZMod q) :
    ∃ k : ℕ, 0 < k ∧ ((TraceStep (R := ZMod q))^[k]) v = v :=
  finite_injective_pure_periodic (traceStep_injective (R := ZMod q)) v

end UnifiedTheory
