namespace BEDC.FKernel.ExternalBinary

inductive BWord where
  | nil
  | bit0 (w : BWord)
  | bit1 (w : BWord)

def append : BWord → BWord → BWord
  | a, .nil => a
  | a, .bit0 b => .bit0 (append a b)
  | a, .bit1 b => .bit1 (append a b)

theorem external_finite_kernel_soundness :
    (∀ w : BWord, append w .nil = w) ∧
      (∀ a b c : BWord, append (append a b) c = append a (append b c)) := by
  constructor
  · intro w
    rfl
  · intro a b c
    induction c with
    | nil =>
        rfl
    | bit0 c ih =>
        exact congrArg BWord.bit0 ih
    | bit1 c ih =>
        exact congrArg BWord.bit1 ih

end BEDC.FKernel.ExternalBinary
