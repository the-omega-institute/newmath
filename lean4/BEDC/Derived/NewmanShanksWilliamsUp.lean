namespace BEDC.Derived.NewmanShanksWilliamsUp

def newmanShanksWilliams : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | n + 2 =>
      2 * newmanShanksWilliams (n + 1) + newmanShanksWilliams n

structure NSWState where
  current : Nat
  previous : Nat

def nswSeed : NSWState :=
  ⟨1, 1⟩

def nswStep : NSWState -> NSWState
  | ⟨current, previous⟩ => ⟨2 * current + previous, current⟩

def nswState : Nat -> NSWState
  | 0 => nswSeed
  | Nat.succ n => nswStep (nswState n)

theorem newmanShanksWilliams_zero :
    newmanShanksWilliams 0 = 1 := by
  rfl

theorem newmanShanksWilliams_one :
    newmanShanksWilliams 1 = 1 := by
  rfl

theorem newmanShanksWilliams_recurrence (n : Nat) :
    newmanShanksWilliams (n + 2) =
      2 * newmanShanksWilliams (n + 1) + newmanShanksWilliams n := by
  rfl

theorem newmanShanksWilliams_two :
    newmanShanksWilliams 2 = 3 := by
  rfl

theorem newmanShanksWilliams_three :
    newmanShanksWilliams 3 = 7 := by
  rfl

theorem newmanShanksWilliams_four :
    newmanShanksWilliams 4 = 17 := by
  rfl

theorem newmanShanksWilliams_five :
    newmanShanksWilliams 5 = 41 := by
  rfl

theorem nswState_zero :
    nswState 0 = nswSeed := by
  rfl

theorem nswState_succ (n : Nat) :
    nswState (Nat.succ n) = nswStep (nswState n) := by
  rfl

theorem nswStep_seed :
    nswStep nswSeed = ⟨3, 1⟩ := by
  rfl

theorem NewmanShanksWilliamsUp_constructive_export :
    newmanShanksWilliams 0 = 1 ∧
      newmanShanksWilliams 1 = 1 ∧
      (∀ n : Nat,
        newmanShanksWilliams (n + 2) =
          2 * newmanShanksWilliams (n + 1) + newmanShanksWilliams n) ∧
      newmanShanksWilliams 5 = 41 ∧
      nswStep nswSeed = ⟨3, 1⟩ := by
  constructor
  · exact newmanShanksWilliams_zero
  · constructor
    · exact newmanShanksWilliams_one
    · constructor
      · intro n
        exact newmanShanksWilliams_recurrence n
      · constructor
        · exact newmanShanksWilliams_five
        · exact nswStep_seed

end BEDC.Derived.NewmanShanksWilliamsUp
