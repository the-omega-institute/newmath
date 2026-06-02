import Mathlib.Data.Fintype.Basic

namespace Classifier

inductive Mark where
  | supported
  | conflicted
  | missing
  deriving DecidableEq, Repr

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

end Classifier
