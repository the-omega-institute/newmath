namespace BEDC.FKernel.ExternalBinary

inductive BWord where
  | nil
  | bit0 (w : BWord)
  | bit1 (w : BWord)

abbrev Mbin : Type := BWord

def append : BWord → BWord → BWord
  | a, .nil => a
  | a, .bit0 b => .bit0 (append a b)
  | a, .bit1 b => .bit1 (append a b)

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

theorem external_finite_kernel_soundness :
    (∀ w : BWord, append w .nil = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) := by
  constructor
  · intro w
    rfl
  · intro a b c
    exact external_append_assoc a b c

end BEDC.FKernel.ExternalBinary
