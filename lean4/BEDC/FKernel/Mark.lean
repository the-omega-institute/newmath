/-! Raw marks and their internal sameness relation. -/
namespace BEDC.FKernel.Mark

inductive BMark where
  | b0
  | b1
  deriving DecidableEq, Repr

def msame : BMark → BMark → Prop := Eq

theorem msame_refl : ∀ m : BMark, msame m m := by
  intro m
  rfl

theorem msame_symm : ∀ {m n : BMark}, msame m n → msame n m := by
  intro m n h
  exact h.symm

theorem msame_trans : ∀ {a b c : BMark}, msame a b → msame b c → msame a c := by
  intro a b c hab hbc
  exact hab.trans hbc

theorem msame_equivalence :
    (∀ m : BMark, msame m m) ∧
      (∀ {m n : BMark}, msame m n → msame n m) ∧
      (∀ {a b c : BMark}, msame a b → msame b c → msame a c) := by
  constructor
  · exact msame_refl
  · constructor
    · exact msame_symm
    · exact msame_trans

theorem not_msame_b0_b1 : msame .b0 .b1 → False := by
  intro h
  cases h

theorem not_msame_b1_b0 : msame .b1 .b0 → False := by
  intro h
  cases h

end BEDC.FKernel.Mark
