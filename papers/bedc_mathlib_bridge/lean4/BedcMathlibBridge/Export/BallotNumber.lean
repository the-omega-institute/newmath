import BedcMathlibBridge.Constructive.BallotNumber

/-!
Export witness for the ballot-number binomial-difference correspondence.
-/

namespace BedcMathlibBridge.Export.BallotNumber

open BedcMathlibBridge.Constructive.BallotNumber

structure BallotNumberExportWitness where
  readback : Nat -> Nat -> Nat
  readback_apply : forall n k : Nat, readback n k = ballotNumber n k
  bedc_choose_diff_apply :
    forall n k : Nat,
      readback n k =
        BEDC.Derived.BinomialIdentitiesUp.C (n + k) k -
          BEDC.Derived.BinomialIdentitiesUp.C (n + k) (Nat.succ k)
  mathlib_choose_diff_apply :
    forall n k : Nat,
      readback n k =
        Nat.choose (n + k) k - Nat.choose (n + k) (Nat.succ k)
  zero_right_apply :
    forall n : Nat, readback n 0 = 1 - Nat.choose n 1

def ballotNumberExport : BallotNumberExportWitness where
  readback := ballotNumber
  readback_apply := by
    intro n k
    rfl
  bedc_choose_diff_apply := ballotNumber_eq_bedc_choose_diff
  mathlib_choose_diff_apply := ballotNumber_eq_nat_choose_diff
  zero_right_apply := ballotNumber_zero_right

theorem ballotNumber_eq_nat_choose_diff (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C (n + k) k -
        BEDC.Derived.BinomialIdentitiesUp.C (n + k) (Nat.succ k) =
      Nat.choose (n + k) k - Nat.choose (n + k) (Nat.succ k) :=
  BedcMathlibBridge.Constructive.BallotNumber.bedc_choose_diff_eq_nat_choose_diff n k

end BedcMathlibBridge.Export.BallotNumber
