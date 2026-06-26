namespace BedcMathlibBridge.Negative

def HollowStatement_Statement : Prop :=
  ∃ n : Nat, n = n

theorem HollowStatement_well_formed : True :=
  True.intro

end BedcMathlibBridge.Negative
