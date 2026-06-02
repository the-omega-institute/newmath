import Mathlib.Data.Fintype.Basic

namespace Classifier

inductive Mark where
  | supported
  | conflicted
  | missing
  deriving DecidableEq, Repr

def allMarks : List Mark :=
  [Mark.supported, Mark.conflicted, Mark.missing]

theorem supported_mem_allMarks : Mark.supported ∈ allMarks := by
  simp [allMarks]

theorem conflicted_mem_allMarks : Mark.conflicted ∈ allMarks := by
  simp [allMarks]

theorem missing_mem_allMarks : Mark.missing ∈ allMarks := by
  simp [allMarks]

theorem mark_mem_allMarks (x : Mark) : x ∈ allMarks := by
  cases x <;> simp [allMarks]

theorem allMarks_complete (x : Mark) :
    x = Mark.supported ∨ x = Mark.conflicted ∨ x = Mark.missing := by
  cases x <;> simp

def sameClass (x y : Mark) : Prop :=
  x = y

theorem sameClass_refl (x : Mark) : sameClass x x := by
  rfl

theorem sameClass_symm {x y : Mark} :
    sameClass x y → sameClass y x := by
  intro h
  exact Eq.symm h

theorem sameClass_trans {x y z : Mark} :
    sameClass x y → sameClass y z → sameClass x z := by
  intro hxy hyz
  exact Eq.trans hxy hyz

theorem sameClass_equivalence : Equivalence sameClass where
  refl := sameClass_refl
  symm := @sameClass_symm
  trans := @sameClass_trans

theorem sameClass_decidable (x y : Mark) :
    sameClass x y ∨ ¬ sameClass x y := by
  unfold sameClass
  exact Decidable.em _

theorem sameClass_eq {x y : Mark} :
    sameClass x y ↔ x = y := by
  rfl

end Classifier
