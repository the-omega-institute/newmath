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

theorem external_append_empty_left : ∀ w : BWord, append .Empty w = w :=
  BEDC.FKernel.Cont.append_empty_left

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

theorem external_append_e1_right (a b : BWord) : append a (.e1 b) = .e1 (append a b) := rfl

theorem external_append_assoc :
    ∀ a b c : BWord, append (append a b) c = append a (append b c) :=
  BEDC.FKernel.Cont.append_assoc

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

theorem external_append_nil_result_inversion :
    ∀ {a b : BWord}, append a b = BHist.Empty → a = BHist.Empty ∧ b = BHist.Empty := by
  intro a b h
  cases b with
  | Empty => exact ⟨h, rfl⟩
  | e0 b => cases h
  | e1 b => cases h

theorem external_append_nil_inversion :
    ∀ {a b : BWord}, append a b = BHist.Empty → a = BHist.Empty ∧ b = BHist.Empty :=
  external_append_nil_result_inversion

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

theorem external_append_right_cancel : ∀ a b c : BWord, append a c = append b c → a = b := by
  intro a b c h
  exact BEDC.FKernel.Cont.append_right_cancel h

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

theorem external_finite_kernel_soundness :
    (∀ w : BWord, append w BHist.Empty = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) :=
  ⟨external_append_empty_right, external_append_assoc⟩

end BEDC.FKernel.ExternalBinary
