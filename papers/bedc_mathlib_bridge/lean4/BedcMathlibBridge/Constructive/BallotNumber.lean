import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.BinomialIdentitiesUp
import Mathlib.Data.Nat.Choose.Basic

/-!
Ballot-number binomial-difference readback.

The BEDC side uses the existing binomial counter `C`. The bridge exposes the
standard choose-difference surface against mathlib `Nat.choose`.
-/

namespace BedcMathlibBridge.Constructive.BallotNumber

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

def ballotNumber (n k : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.BinomialIdentitiesUp.C (n + k) k -
    BEDC.Derived.BinomialIdentitiesUp.C (n + k) (Nat.succ k)

theorem ballotNumber_eq_bedc_choose_diff (n k : Nat) :
    ballotNumber n k =
      BEDC.Derived.BinomialIdentitiesUp.C (n + k) k -
        BEDC.Derived.BinomialIdentitiesUp.C (n + k) (Nat.succ k) := by
  rfl

theorem bedc_choose_diff_eq_nat_choose_diff (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C (n + k) k -
        BEDC.Derived.BinomialIdentitiesUp.C (n + k) (Nat.succ k) =
      Nat.choose (n + k) k - Nat.choose (n + k) (Nat.succ k) := by
  rw [C_eq_nat_choose (n + k) k, C_eq_nat_choose (n + k) (Nat.succ k)]

theorem ballotNumber_eq_nat_choose_diff (n k : Nat) :
    ballotNumber n k =
      Nat.choose (n + k) k - Nat.choose (n + k) (Nat.succ k) := by
  rw [ballotNumber_eq_bedc_choose_diff]
  exact bedc_choose_diff_eq_nat_choose_diff n k

theorem ballotNumber_zero_right (n : Nat) :
    ballotNumber n 0 = 1 - Nat.choose n 1 := by
  rw [ballotNumber_eq_nat_choose_diff]
  rw [Nat.choose_zero_right]
  rw [Nat.add_zero]

end BedcMathlibBridge.Constructive.BallotNumber
