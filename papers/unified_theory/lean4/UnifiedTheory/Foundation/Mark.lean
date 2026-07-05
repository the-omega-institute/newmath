import Mathlib.Logic.Function.Basic

namespace UnifiedTheory

inductive Mark where
  | zero : Mark
  | one : Mark
deriving DecidableEq, Repr

namespace Mark

def sigma : Mark -> Mark
  | zero => one
  | one => zero

theorem sigma_zero : sigma zero = one := rfl

theorem sigma_one : sigma one = zero := rfl

theorem sigma_involutive : Function.Involutive sigma := by
  intro x
  cases x <;> rfl

theorem sigma_ne_id : sigma zero ≠ zero := by
  intro h
  cases h

theorem sigma_nontrivial : sigma zero = one ∧ sigma one = zero :=
  ⟨sigma_zero, sigma_one⟩

end Mark
end UnifiedTheory
