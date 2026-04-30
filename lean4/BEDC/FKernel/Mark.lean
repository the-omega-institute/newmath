/-! Raw marks and their internal sameness relation. -/
namespace BEDC.FKernel.Mark

inductive BMark where
  | b0
  | b1
  deriving DecidableEq, Repr

def msame : BMark → BMark → Prop := Eq

theorem msame_iff_eq {m n : BMark} : msame m n ↔ m = n := by
  rfl

theorem msame_refl : ∀ m : BMark, msame m m := by
  intro m
  rfl

theorem msame_generated_rules : msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 := by
  constructor
  · rfl
  · rfl

theorem BMark_generated_cases (m : BMark) : m = BMark.b0 ∨ m = BMark.b1 := by
  cases m with
  | b0 =>
      exact Or.inl rfl
  | b1 =>
      exact Or.inr rfl

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

theorem mark_sameness_equivalence :
    (forall m : BMark, msame m m) /\
      (forall {m n : BMark}, msame m n -> msame n m) /\
      (forall {a b c : BMark}, msame a b -> msame b c -> msame a c) := by
  exact msame_equivalence

theorem msame_internal_equivalence_spine :
    (forall m : BMark, msame m m) /\
      (forall {m n : BMark}, msame m n -> msame n m) /\
      (forall {a b c : BMark}, msame a b -> msame b c -> msame a c) := by
  exact msame_equivalence

theorem not_msame_b0_b1 : msame .b0 .b1 → False := by
  intro h
  cases h

theorem not_msame_b1_b0 : msame .b1 .b0 → False := by
  intro h
  cases h

theorem msame_no_confusion : (msame .b0 .b1 → False) ∧ (msame .b1 .b0 → False) := by
  constructor
  · exact not_msame_b0_b1
  · exact not_msame_b1_b0

theorem mark_no_confusion :
    (msame BMark.b0 BMark.b1 -> False) /\ (msame BMark.b1 BMark.b0 -> False) := by
  constructor
  · exact not_msame_b0_b1
  · exact not_msame_b1_b0

theorem msame_cross_iff_false :
    (msame BMark.b0 BMark.b1 ↔ False) ∧ (msame BMark.b1 BMark.b0 ↔ False) := by
  constructor
  · constructor
    · exact not_msame_b0_b1
    · intro impossible
      cases impossible
  · constructor
    · exact not_msame_b1_b0
    · intro impossible
      cases impossible

theorem msame_cross_impossible {m n : BMark} :
    ((m = BMark.b0 ∧ n = BMark.b1) ∨ (m = BMark.b1 ∧ n = BMark.b0)) →
      msame m n → False := by
  intro cross same
  cases cross with
  | inl left =>
      cases left.left
      cases left.right
      exact not_msame_b0_b1 same
  | inr right =>
      cases right.left
      cases right.right
      exact not_msame_b1_b0 same

theorem msame_constructor_characterization {m n : BMark} :
    msame m n ↔ (m = BMark.b0 ∧ n = BMark.b0) ∨ (m = BMark.b1 ∧ n = BMark.b1) := by
  constructor
  · intro h
    cases h
    cases m with
    | b0 =>
        exact Or.inl ⟨rfl, rfl⟩
    | b1 =>
        exact Or.inr ⟨rfl, rfl⟩
  · intro h
    cases h with
    | inl hb0 =>
        cases hb0.left
        cases hb0.right
        rfl
    | inr hb1 =>
        cases hb1.left
        cases hb1.right
        rfl

theorem msame_cases {m n : BMark} :
    msame m n -> (m = BMark.b0 /\ n = BMark.b0) \/ (m = BMark.b1 /\ n = BMark.b1) := by
  intro h
  exact msame_constructor_characterization.mp h

end BEDC.FKernel.Mark
