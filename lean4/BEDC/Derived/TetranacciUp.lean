namespace BEDC.Derived.TetranacciUp

def tetranacci : Nat -> Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | n + 4 =>
      tetranacci n + tetranacci (n + 1) +
        tetranacci (n + 2) + tetranacci (n + 3)

structure State4 where
  top : Nat
  upper : Nat
  lower : Nat
  bottom : Nat

def tetranacciSeed : State4 :=
  ⟨1, 0, 0, 0⟩

def tetranacciStep : State4 -> State4
  | ⟨top, upper, lower, bottom⟩ => ⟨top + upper + lower + bottom, top, upper, lower⟩

def tetranacciState : Nat -> State4
  | 0 => tetranacciSeed
  | Nat.succ n => tetranacciStep (tetranacciState n)

theorem tetranacci_zero :
    tetranacci 0 = 0 := by
  rfl

theorem tetranacci_one :
    tetranacci 1 = 0 := by
  rfl

theorem tetranacci_two :
    tetranacci 2 = 0 := by
  rfl

theorem tetranacci_three :
    tetranacci 3 = 1 := by
  rfl

theorem tetranacci_recurrence (n : Nat) :
    tetranacci (n + 4) =
      tetranacci n + tetranacci (n + 1) +
        tetranacci (n + 2) + tetranacci (n + 3) := by
  rfl

theorem tetranacci_four :
    tetranacci 4 = 1 := by
  rfl

theorem tetranacci_five :
    tetranacci 5 = 2 := by
  rfl

theorem tetranacci_six :
    tetranacci 6 = 4 := by
  rfl

theorem tetranacci_seven :
    tetranacci 7 = 8 := by
  rfl

theorem tetranacciState_zero :
    tetranacciState 0 = tetranacciSeed := by
  rfl

theorem tetranacciState_succ (n : Nat) :
    tetranacciState (Nat.succ n) = tetranacciStep (tetranacciState n) := by
  rfl

theorem tetranacciStep_seed :
    tetranacciStep tetranacciSeed = ⟨1, 1, 0, 0⟩ := by
  rfl

theorem TetranacciUp_constructive_export :
    tetranacci 0 = 0 ∧
      tetranacci 1 = 0 ∧
      tetranacci 2 = 0 ∧
      tetranacci 3 = 1 ∧
      (∀ n : Nat,
        tetranacci (n + 4) =
          tetranacci n + tetranacci (n + 1) +
            tetranacci (n + 2) + tetranacci (n + 3)) ∧
      tetranacci 7 = 8 ∧
      tetranacciStep tetranacciSeed = ⟨1, 1, 0, 0⟩ := by
  constructor
  · exact tetranacci_zero
  · constructor
    · exact tetranacci_one
    · constructor
      · exact tetranacci_two
      · constructor
        · exact tetranacci_three
        · constructor
          · intro n
            exact tetranacci_recurrence n
          · constructor
            · exact tetranacci_seven
            · exact tetranacciStep_seed

end BEDC.Derived.TetranacciUp
