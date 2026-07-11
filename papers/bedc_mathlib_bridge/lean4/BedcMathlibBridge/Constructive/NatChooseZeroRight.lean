import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.NatChooseZeroRight

private def mathlibNatChooseZeroRightProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.choose n 0 = 1 := Nat.choose_zero_right
  ()

def chooseZeroRightReadback (n : Nat) : Nat.choose n 0 = 1 :=
  let _ := mathlibNatChooseZeroRightProvenanceAnchor
  Nat.choose_zero_right n

theorem chooseZeroRightReadback_eq_nat_choose_zero_right (n : Nat) :
    chooseZeroRightReadback n = Nat.choose_zero_right n := by
  rfl

end BedcMathlibBridge.Constructive.NatChooseZeroRight
