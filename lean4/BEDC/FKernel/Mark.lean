/-! Raw marks and their internal sameness relation. -/
namespace BEDC.FKernel.Mark


axiom BMark : Type
axiom b0 : BMark
axiom b1 : BMark
axiom msame : BMark → BMark → Prop

theorem msame_refl : ∀ m : BMark, msame m m := by
  sorry

theorem msame_symm : ∀ {m n : BMark}, msame m n → msame n m := by
  sorry

theorem msame_trans : ∀ {a b c : BMark}, msame a b → msame b c → msame a c := by
  sorry

theorem not_msame_b0_b1 : msame b0 b1 → False := by
  sorry

theorem not_msame_b1_b0 : msame b1 b0 → False := by
  sorry

end BEDC.FKernel.Mark
