namespace BEDC.Derived.MarkovTripleUp

structure MarkovTriple where
  x : Nat
  y : Nat
  z : Nat
  equation : x * x + y * y + z * z = 3 * x * y * z

def markovRoot : MarkovTriple :=
  { x := 1, y := 1, z := 1, equation := by rfl }

def markovOneOneTwo : MarkovTriple :=
  { x := 1, y := 1, z := 2, equation := by rfl }

def markovOneTwoFive : MarkovTriple :=
  { x := 1, y := 2, z := 5, equation := by rfl }

theorem markovRoot_equation :
    markovRoot.x * markovRoot.x + markovRoot.y * markovRoot.y +
        markovRoot.z * markovRoot.z =
      3 * markovRoot.x * markovRoot.y * markovRoot.z := by
  exact markovRoot.equation

theorem markovOneOneTwo_equation :
    markovOneOneTwo.x * markovOneOneTwo.x +
        markovOneOneTwo.y * markovOneOneTwo.y +
        markovOneOneTwo.z * markovOneOneTwo.z =
      3 * markovOneOneTwo.x * markovOneOneTwo.y * markovOneOneTwo.z := by
  exact markovOneOneTwo.equation

theorem markovOneTwoFive_equation :
    markovOneTwoFive.x * markovOneTwoFive.x +
        markovOneTwoFive.y * markovOneTwoFive.y +
        markovOneTwoFive.z * markovOneTwoFive.z =
      3 * markovOneTwoFive.x * markovOneTwoFive.y * markovOneTwoFive.z := by
  exact markovOneTwoFive.equation

theorem markovConcrete_z_values :
    markovRoot.z = 1 ∧
      markovOneOneTwo.z = 2 ∧
      markovOneTwoFive.z = 5 := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem MarkovTripleUp_constructive_export :
    markovRoot.x = 1 ∧
      markovRoot.y = 1 ∧
      markovRoot.z = 1 ∧
      markovOneOneTwo.z = 2 ∧
      markovOneTwoFive.z = 5 ∧
      markovRoot.x * markovRoot.x + markovRoot.y * markovRoot.y +
          markovRoot.z * markovRoot.z =
        3 * markovRoot.x * markovRoot.y * markovRoot.z ∧
      markovOneOneTwo.x * markovOneOneTwo.x +
          markovOneOneTwo.y * markovOneOneTwo.y +
          markovOneOneTwo.z * markovOneOneTwo.z =
        3 * markovOneOneTwo.x * markovOneOneTwo.y * markovOneOneTwo.z ∧
      markovOneTwoFive.x * markovOneTwoFive.x +
          markovOneTwoFive.y * markovOneTwoFive.y +
          markovOneTwoFive.z * markovOneTwoFive.z =
        3 * markovOneTwoFive.x * markovOneTwoFive.y * markovOneTwoFive.z := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · exact markovRoot_equation
            · constructor
              · exact markovOneOneTwo_equation
              · exact markovOneTwoFive_equation

end BEDC.Derived.MarkovTripleUp
