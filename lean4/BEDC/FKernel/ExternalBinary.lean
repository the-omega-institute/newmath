import BEDC.FKernel.Hist
import BEDC.FKernel.Cont

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont (append_empty_left append_empty_right append_assoc append_right_cancel)

/-! External binary metamodel: shows the kernel rules are not empty by
exhibiting `BHist` itself as the binary-word interpretation. `BWord` is a
type alias for `BHist`; constructors `.Empty / .e0 / .e1` play the role of
nil / bit0 / bit1, and `append` is reused from `BEDC.FKernel.Cont`. -/

abbrev BWord : Type := BHist
abbrev Mbin : Type := BWord

theorem Mbin_eq_BHist : Mbin = BHist := by
  rfl

theorem Mbin_reuses_kernel_history : (Mbin = BHist) ∧ (BWord = BHist) := by
  constructor
  · rfl
  · rfl

theorem external_model_reuses_kernel_histories :
    (Mbin = BHist) /\ (BWord = BHist) /\
      (forall w : BWord, BHist.Empty = BHist.e0 w -> False) := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro _ h
      cases h

/-- Reuse the kernel-level continuation function as the metamodel's append. -/
abbrev append : BWord → BWord → BWord := BEDC.FKernel.Cont.append

def bwordLength : BWord → Nat
  | .Empty => 0
  | .e0 w => Nat.succ (bwordLength w)
  | .e1 w => Nat.succ (bwordLength w)

theorem external_append_e0_right (a b : BWord) : append a (.e0 b) = .e0 (append a b) := rfl

theorem bwordLength_append : ∀ a b : BWord, bwordLength (append a b) = bwordLength a + bwordLength b := by
  intro a b
  induction b with
  | Empty =>
      rfl
  | e0 b ih =>
      exact congrArg Nat.succ ih
  | e1 b ih =>
      exact congrArg Nat.succ ih

theorem external_append_length : ∀ a b : BWord, bwordLength (append a b) = bwordLength a + bwordLength b :=
  bwordLength_append

theorem external_append_empty_left : ∀ w : BWord, append .Empty w = w := by
  intro w
  induction w with
  | Empty =>
      rfl
  | e0 w ih =>
      exact congrArg BHist.e0 ih
  | e1 w ih =>
      exact congrArg BHist.e1 ih

theorem external_append_empty_right : ∀ w : BWord, append w .Empty = w :=
  BEDC.FKernel.Cont.append_empty_right

theorem external_append_unit_laws :
    (∀ w : BWord, append BHist.Empty w = w) ∧
      (∀ w : BWord, append w BHist.Empty = w) :=
  ⟨external_append_empty_left, external_append_empty_right⟩

theorem external_append_left_absorb_empty :
    ∀ {a b : BWord}, append a b = b → a = BHist.Empty := by
  intro a b h
  induction b with
  | Empty =>
      exact h
  | e0 b ih =>
      exact ih (BHist.e0.inj h)
  | e1 b ih =>
      exact ih (BHist.e1.inj h)

theorem external_append_left_absorb_empty_iff {a b : BWord} :
    append a b = b <-> a = BHist.Empty := by
  constructor
  · intro h
    exact external_append_left_absorb_empty h
  · intro h
    cases h
    exact external_append_empty_left b

theorem external_append_e1_right (a b : BWord) : append a (.e1 b) = .e1 (append a b) := rfl

theorem external_append_bit_constructor_rules :
    (∀ a b : BWord, append a (.e0 b) = .e0 (append a b)) ∧
      (∀ a b : BWord, append a (.e1 b) = .e1 (append a b)) := by
  constructor
  case left =>
    intro a b
    rfl
  case right =>
    intro a b
    rfl

theorem external_append_assoc :
    ∀ a b c : BWord, append (append a b) c = append a (append b c) := by
  intro a b c
  induction c with
  | Empty =>
      rfl
  | e0 c ih =>
      exact congrArg BHist.e0 ih
  | e1 c ih =>
      exact congrArg BHist.e1 ih

theorem external_append_assoc_four :
    ∀ a b c d : BWord, append (append (append a b) c) d =
      append a (append b (append c d)) := by
  intro a b c d
  exact Eq.trans (external_append_assoc (append a b) c d) (external_append_assoc a b (append c d))

theorem external_word_no_confusion :
    (∀ w : BWord, BHist.Empty = BHist.e0 w → False) ∧
      (∀ w : BWord, BHist.Empty = BHist.e1 w → False) ∧
      (∀ a b : BWord, BHist.e0 a = BHist.e1 b → False) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ _ h; cases h

private theorem nat_eq_add_succ_false (n m : Nat) : n = n + m + 1 → False := by
  intro h
  exact (Nat.lt_irrefl n) (Nat.lt_of_lt_of_eq (Nat.lt_add_of_pos_right (Nat.succ_pos m)) h.symm)

theorem external_append_right_length_zero {a b : BWord} :
    bwordLength (append a b) = bwordLength a → b = BHist.Empty := by
  intro h
  cases b with
  | Empty => rfl
  | e0 b =>
      simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at h
      exact False.elim (nat_eq_add_succ_false (bwordLength a) (bwordLength b) h.symm)
  | e1 b =>
      simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at h
      exact False.elim (nat_eq_add_succ_false (bwordLength a) (bwordLength b) h.symm)

theorem external_append_length_eq_left_iff_right_empty {a b : BWord} :
    bwordLength (append a b) = bwordLength a ↔ b = BHist.Empty := by
  constructor
  · intro h
    exact external_append_right_length_zero h
  · intro h
    cases h
    rfl

theorem external_length_zero_iff_nil (w : BWord) : bwordLength w = 0 ↔ w = BHist.Empty := by
  constructor
  · intro h
    cases w with
    | Empty => rfl
    | e0 w => cases h
    | e1 w => cases h
  · intro h
    cases h
    rfl

theorem external_append_left_length_zero :
    forall {a b : BWord}, bwordLength (append a b) = bwordLength b -> a = BHist.Empty := by
  intro a b h
  induction b generalizing a with
  | Empty =>
      exact Iff.mp (external_length_zero_iff_nil a) h
  | e0 b ih =>
      exact ih (Nat.succ.inj h)
  | e1 b ih =>
      exact ih (Nat.succ.inj h)

theorem external_append_length_eq_right_iff_left_empty {a b : BWord} :
    bwordLength (append a b) = bwordLength b <-> a = BHist.Empty := by
  constructor
  · intro h
    exact external_append_left_length_zero h
  · intro h
    cases h
    exact congrArg bwordLength (external_append_empty_left b)

theorem external_append_nil_result_inversion :
    ∀ {a b : BWord}, append a b = BHist.Empty → a = BHist.Empty ∧ b = BHist.Empty := by
  intro a b h
  cases b with
  | Empty => exact ⟨h, rfl⟩
  | e0 b => cases h
  | e1 b => cases h

theorem external_append_length_zero_pair {a b : BWord} :
    bwordLength (append a b) = 0 -> a = BHist.Empty /\ b = BHist.Empty := by
  intro h
  exact external_append_nil_result_inversion ((external_length_zero_iff_nil (append a b)).mp h)

theorem external_append_nil_inversion :
    ∀ {a b : BWord}, append a b = BHist.Empty → a = BHist.Empty ∧ b = BHist.Empty :=
  external_append_nil_result_inversion

theorem external_append_empty_result_iff {a b : BWord} :
    append a b = BHist.Empty ↔ a = BHist.Empty ∧ b = BHist.Empty := by
  constructor
  · intro h
    exact external_append_nil_result_inversion h
  · intro h
    cases h with
    | intro ha hb =>
        cases ha
        cases hb
        rfl

theorem external_append_bit_result_inversion :
    (∀ {a b r : BWord}, append a b = BHist.e0 r →
      (b = BHist.Empty ∧ a = BHist.e0 r) ∨
        (∃ b0 : BWord, b = BHist.e0 b0 ∧ append a b0 = r)) ∧
    (∀ {a b r : BWord}, append a b = BHist.e1 r →
      (b = BHist.Empty ∧ a = BHist.e1 r) ∨
        (∃ b0 : BWord, b = BHist.e1 b0 ∧ append a b0 = r)) := by
  refine ⟨?_, ?_⟩
  · intro a b r h
    cases b with
    | Empty => exact Or.inl ⟨rfl, h⟩
    | e0 b0 => exact Or.inr ⟨b0, rfl, BHist.e0.inj h⟩
    | e1 b0 => cases h
  · intro a b r h
    cases b with
    | Empty => exact Or.inl ⟨rfl, h⟩
    | e0 b0 => cases h
    | e1 b0 => exact Or.inr ⟨b0, rfl, BHist.e1.inj h⟩

theorem external_append_bit0_result_inversion :
    ∀ {a b r : BWord}, append a b = BHist.e0 r →
      (b = BHist.Empty ∧ a = BHist.e0 r) ∨
        (∃ b0 : BWord, b = BHist.e0 b0 ∧ append a b0 = r) :=
  external_append_bit_result_inversion.left

theorem external_append_bit1_result_inversion :
    ∀ {a b r : BWord}, append a b = BHist.e1 r →
      (b = BHist.Empty ∧ a = BHist.e1 r) ∨
        (∃ b0 : BWord, b = BHist.e1 b0 ∧ append a b0 = r) :=
  external_append_bit_result_inversion.right

theorem external_append_bit_result_iff :
    (∀ {a b r : BWord}, append a b = BHist.e0 r ↔
      (b = BHist.Empty ∧ a = BHist.e0 r) ∨
        (∃ b0 : BWord, b = BHist.e0 b0 ∧ append a b0 = r)) ∧
    (∀ {a b r : BWord}, append a b = BHist.e1 r ↔
      (b = BHist.Empty ∧ a = BHist.e1 r) ∨
        (∃ b1 : BWord, b = BHist.e1 b1 ∧ append a b1 = r)) := by
  constructor
  · intro a b r
    constructor
    · intro h
      exact external_append_bit_result_inversion.left h
    · intro h
      cases h with
      | inl emptyResult =>
          cases emptyResult with
          | intro hb ha =>
              cases hb
              cases ha
              rfl
      | inr tailResult =>
          cases tailResult with
          | intro b0 result =>
              cases result with
              | intro hb tail =>
                  cases hb
                  exact congrArg BHist.e0 tail
  · intro a b r
    constructor
    · intro h
      exact external_append_bit_result_inversion.right h
    · intro h
      cases h with
      | inl emptyResult =>
          cases emptyResult with
          | intro hb ha =>
              cases hb
              cases ha
              rfl
      | inr tailResult =>
          cases tailResult with
          | intro b1 result =>
              cases result with
              | intro hb tail =>
                  cases hb
                  exact congrArg BHist.e1 tail

theorem external_append_constructor_result_inversion :
    (∀ {a b r : BWord}, append a b = BHist.e0 r →
      (b = BHist.Empty ∧ a = BHist.e0 r) ∨
        (∃ b0 : BWord, b = BHist.e0 b0 ∧ append a b0 = r)) ∧
    (∀ {a b r : BWord}, append a b = BHist.e1 r →
      (b = BHist.Empty ∧ a = BHist.e1 r) ∨
        (∃ b1 : BWord, b = BHist.e1 b1 ∧ append a b1 = r)) := by
  exact external_append_bit_result_inversion

theorem external_append_right_cancel : ∀ a b c : BWord, append a c = append b c → a = b := by
  intro a b c h
  induction c generalizing a b with
  | Empty =>
      exact h
  | e0 c ih =>
      exact ih a b (BHist.e0.inj h)
  | e1 c ih =>
      exact ih a b (BHist.e1.inj h)

theorem external_append_right_cancel_hsame :
    forall {a b c : BWord}, hsame (append a c) (append b c) -> hsame a b := by
  intro a b c same
  induction c generalizing a b with
  | Empty =>
      exact same
  | e0 c ih =>
      exact ih (BHist.e0.inj same)
  | e1 c ih =>
      exact ih (BHist.e1.inj same)

theorem external_append_right_cancel_by_induction :
    forall {a b c : BWord}, append a c = append b c -> hsame a b := by
  intro a b c same
  induction c with
  | Empty =>
      exact same
  | e0 c ih =>
      exact ih (BHist.e0.inj same)
  | e1 c ih =>
      exact ih (BHist.e1.inj same)

theorem external_append_left_cancel : ∀ a b c : BWord, append c a = append c b → a = b := by
  intro a
  induction a with
  | Empty =>
      intro b c h
      cases b with
      | Empty => rfl
      | e0 b =>
          have hlen := congrArg bwordLength h
          simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength b) hlen)
      | e1 b =>
          have hlen := congrArg bwordLength h
          simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength b) hlen)
  | e0 a ih =>
      intro b c h
      cases b with
      | Empty =>
          have hlen := congrArg bwordLength h
          simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength a) hlen.symm)
      | e0 b => exact congrArg BHist.e0 (ih b c (BHist.e0.inj h))
      | e1 b => cases h
  | e1 a ih =>
      intro b c h
      cases b with
      | Empty =>
          have hlen := congrArg bwordLength h
          simp [append, BEDC.FKernel.Cont.append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength a) hlen.symm)
      | e0 b => cases h
      | e1 b => exact congrArg BHist.e1 (ih b c (BHist.e1.inj h))

theorem external_append_left_cancel_hsame :
    ∀ {a b c : BWord}, hsame (append c a) (append c b) → hsame a b := by
  intro a b c same
  exact external_append_left_cancel a b c same

theorem external_append_cancel_hsame_pair :
    (∀ {a b c : BWord}, hsame (append a c) (append b c) → hsame a b) ∧
      (∀ {a b c : BWord}, hsame (append c a) (append c b) → hsame a b) := by
  constructor
  · intro a b c same
    exact external_append_right_cancel_hsame same
  · intro a b c same
    exact external_append_left_cancel_hsame same

theorem external_append_cancel_pair :
    (forall {a b c : BWord}, append a c = append b c -> a = b) /\
      (forall {a b c : BWord}, append c a = append c b -> a = b) := by
  constructor
  · intro a b c same
    exact external_append_right_cancel a b c same
  · intro a b c same
    exact external_append_left_cancel a b c same

theorem external_append_right_unit_unique {a b : BWord} : append a b = a → b = BHist.Empty := by
  intro h
  have hright : append a b = append a BHist.Empty :=
    Eq.trans h (external_append_empty_right a).symm
  exact external_append_left_cancel b BHist.Empty a hright

theorem external_append_right_unit_iff {a b : BWord} :
    append a b = a ↔ b = BHist.Empty := by
  constructor
  · intro h
    exact external_append_right_unit_unique h
  · intro h
    cases h
    exact external_append_empty_right a

theorem external_append_unit_uniqueness_pair :
    (∀ {a b : BWord}, append a b = b → a = BHist.Empty) ∧
      (∀ {a b : BWord}, append a b = a → b = BHist.Empty) := by
  exact ⟨external_append_left_absorb_empty, external_append_right_unit_unique⟩

theorem external_finite_kernel_soundness :
    (∀ w : BWord, append w BHist.Empty = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) :=
  ⟨external_append_empty_right, external_append_assoc⟩

theorem external_finite_kernel_soundness_full :
    (∀ w : BWord, append BHist.Empty w = w) ∧
      (∀ w : BWord, append w BHist.Empty = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) ∧
      (∀ a b c : BWord, append a c = append b c → a = b) := by
  constructor
  · exact external_append_empty_left
  · constructor
    · exact external_append_empty_right
    · constructor
      · exact external_append_assoc
      · exact external_append_right_cancel

theorem external_model_soundness_finite_kernel :
    (forall w : BWord, append BHist.Empty w = w) /\
      (forall w : BWord, append w BHist.Empty = w) /\
      (forall a b c : BWord, append (append a b) c = append a (append b c)) /\
      (forall a b c : BWord, append a c = append b c -> a = b) /\
      (forall a b c : BWord, append c a = append c b -> a = b) /\
      (forall a b : BWord, bwordLength (append a b) = bwordLength a + bwordLength b) := by
  exact ⟨external_append_empty_left, external_append_empty_right, external_append_assoc,
    external_append_right_cancel, external_append_left_cancel, external_append_length⟩

end BEDC.FKernel.ExternalBinary
