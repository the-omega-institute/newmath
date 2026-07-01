namespace BEDC.Derived.RecamanSequenceUp

def listContainsNat (target : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs =>
      if x = target then true else listContainsNat target xs

def recamanStep (history : List Nat) (current n : Nat) : Nat :=
  let down := current - n
  if down = 0 then current + n
  else if listContainsNat down history then current + n
  else down

def recamanPrefixAux : Nat -> Nat -> List Nat -> List Nat
  | 0, _current, history => history
  | Nat.succ fuel, current, history =>
      let index := history.length
      let next := recamanStep history current index
      recamanPrefixAux fuel next (history ++ [next])

def recamanPrefix (fuel : Nat) : List Nat :=
  recamanPrefixAux fuel 0 [0]

theorem listContainsNat_nil (target : Nat) :
    listContainsNat target [] = false := by
  rfl

theorem recamanPrefix_zero :
    recamanPrefix 0 = [0] := by
  rfl

theorem recamanStep_first :
    recamanStep [0] 0 1 = 1 := by
  rfl

theorem recamanPrefix_three :
    recamanPrefix 3 = [0, 1, 3, 6] := by
  rfl

theorem recamanPrefix_seven :
    recamanPrefix 7 = [0, 1, 3, 6, 2, 7, 13, 20] := by
  rfl

theorem RecamanSequenceUp_constructive_export :
    recamanPrefix 0 = [0] ∧
      recamanStep [0] 0 1 = 1 ∧
      recamanPrefix 3 = [0, 1, 3, 6] ∧
      recamanPrefix 7 = [0, 1, 3, 6, 2, 7, 13, 20] := by
  constructor
  · exact recamanPrefix_zero
  · constructor
    · exact recamanStep_first
    · constructor
      · exact recamanPrefix_three
      · exact recamanPrefix_seven

end BEDC.Derived.RecamanSequenceUp
