namespace BEDC.FKernel.ExternalBinary

inductive BWord where
  | nil
  | bit0 (w : BWord)
  | bit1 (w : BWord)

abbrev Mbin : Type := BWord

def bwordLength : BWord → Nat
  | .nil => 0
  | .bit0 w => Nat.succ (bwordLength w)
  | .bit1 w => Nat.succ (bwordLength w)

def append : BWord → BWord → BWord
  | a, .nil => a
  | a, .bit0 b => .bit0 (append a b)
  | a, .bit1 b => .bit1 (append a b)

theorem external_append_bit1_right (a b : BWord) : append a (.bit1 b) = .bit1 (append a b) := by
  rfl

theorem bwordLength_append : ∀ a b : BWord, bwordLength (append a b) = bwordLength a + bwordLength b := by
  intro a b
  induction b with
  | nil =>
      rfl
  | bit0 b ih =>
      exact congrArg Nat.succ ih
  | bit1 b ih =>
      exact congrArg Nat.succ ih

private theorem nat_eq_add_succ_false (n m : Nat) : n = n + m + 1 -> False := by
  intro h
  have hlt : n < n + m + 1 := by
    exact Nat.lt_add_of_pos_right (Nat.succ_pos m)
  exact (Nat.lt_irrefl n) (Nat.lt_of_lt_of_eq hlt h.symm)

theorem external_append_empty_left : forall w : BWord, append .nil w = w := by
  intro w
  induction w with
  | nil =>
      rfl
  | bit0 w ih =>
      exact congrArg BWord.bit0 ih
  | bit1 w ih =>
      exact congrArg BWord.bit1 ih

theorem external_append_empty_right : forall w : BWord, append w .nil = w := by
  intro w
  rfl

theorem external_append_unit_laws :
    (forall w : BWord, append BWord.nil w = w) /\
      (forall w : BWord, append w BWord.nil = w) := by
  constructor
  · exact external_append_empty_left
  · exact external_append_empty_right

theorem external_word_no_confusion :
    (forall w : BWord, BWord.nil = BWord.bit0 w -> False) /\
      (forall w : BWord, BWord.nil = BWord.bit1 w -> False) /\
      (forall a b : BWord, BWord.bit0 a = BWord.bit1 b -> False) := by
  constructor
  · intro w h
    cases h
  · constructor
    · intro w h
      cases h
    · intro a b h
      cases h

theorem external_append_nil_result_inversion :
    ∀ {a b : BWord}, append a b = BWord.nil → a = BWord.nil ∧ b = BWord.nil := by
  intro a b h
  cases b with
  | nil =>
      constructor
      · exact h
      · rfl
  | bit0 b =>
      cases h
  | bit1 b =>
      cases h

theorem external_append_nil_inversion :
    ∀ {a b : BWord}, append a b = BWord.nil → a = BWord.nil ∧ b = BWord.nil := by
  exact external_append_nil_result_inversion

theorem external_append_bit_result_inversion :
    (∀ {a b r : BWord}, append a b = BWord.bit0 r ->
      (b = BWord.nil ∧ a = BWord.bit0 r) ∨
        (∃ b0 : BWord, b = BWord.bit0 b0 ∧ append a b0 = r)) ∧
    (∀ {a b r : BWord}, append a b = BWord.bit1 r ->
      (b = BWord.nil ∧ a = BWord.bit1 r) ∨
        (∃ b0 : BWord, b = BWord.bit1 b0 ∧ append a b0 = r)) := by
  constructor
  · intro a b r h
    cases b with
    | nil =>
        exact Or.inl (And.intro rfl h)
    | bit0 b0 =>
        exact Or.inr (Exists.intro b0 (And.intro rfl (BWord.bit0.inj h)))
    | bit1 b0 =>
        cases h
  · intro a b r h
    cases b with
    | nil =>
        exact Or.inl (And.intro rfl h)
    | bit0 b0 =>
        cases h
    | bit1 b0 =>
        exact Or.inr (Exists.intro b0 (And.intro rfl (BWord.bit1.inj h)))

theorem external_append_assoc :
    forall a b c : BWord, append (append a b) c = append a (append b c) := by
  intro a b c
  induction c with
  | nil =>
      rfl
  | bit0 c ih =>
      exact congrArg BWord.bit0 ih
  | bit1 c ih =>
      exact congrArg BWord.bit1 ih

theorem external_append_assoc_four :
    forall a b c d : BWord, append (append (append a b) c) d =
      append a (append b (append c d)) := by
  intro a b c d
  exact Eq.trans
    (external_append_assoc (append a b) c d)
    (external_append_assoc a b (append c d))

theorem external_append_right_cancel : forall a b c : BWord, append a c = append b c -> a = b := by
  intro a b c h
  induction c with
  | nil =>
      exact h
  | bit0 c ih =>
      exact ih (BWord.bit0.inj h)
  | bit1 c ih =>
      exact ih (BWord.bit1.inj h)

theorem external_append_left_cancel : ∀ a b c : BWord, append c a = append c b → a = b := by
  intro a
  induction a with
  | nil =>
      intro b c h
      cases b with
      | nil =>
          rfl
      | bit0 b =>
          have hlen := congrArg bwordLength h
          simp [append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength b) hlen)
      | bit1 b =>
          have hlen := congrArg bwordLength h
          simp [append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength b) hlen)
  | bit0 a ih =>
      intro b c h
      cases b with
      | nil =>
          have hlen := congrArg bwordLength h
          simp [append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength a) hlen.symm)
      | bit0 b =>
          exact congrArg BWord.bit0 (ih b c (BWord.bit0.inj h))
      | bit1 b =>
          cases h
  | bit1 a ih =>
      intro b c h
      cases b with
      | nil =>
          have hlen := congrArg bwordLength h
          simp [append, bwordLength, bwordLength_append] at hlen
          exact False.elim (nat_eq_add_succ_false (bwordLength c) (bwordLength a) hlen.symm)
      | bit0 b =>
          cases h
      | bit1 b =>
          exact congrArg BWord.bit1 (ih b c (BWord.bit1.inj h))

theorem external_finite_kernel_soundness :
    (∀ w : BWord, append w .nil = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) := by
  constructor
  · intro w
    rfl
  · intro a b c
    exact external_append_assoc a b c

end BEDC.FKernel.ExternalBinary
