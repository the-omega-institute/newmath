import BedcMathlibBridge.Constructive.Binomial
import BedcMathlibBridge.Constructive.Derangement
import BEDC.Derived.RencontresNumberUp

namespace BedcMathlibBridge.Constructive.Rencontres

private def mathlibRencontresProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k :=
    fun _ _ => rfl
  let _ : forall n : Nat, numDerangements n = numDerangements n :=
    fun _ => rfl
  ()

def readback (n k : Nat) : Nat :=
  let _ := mathlibRencontresProvenanceAnchor
  BEDC.Derived.RencontresNumberUp.rencontresNumber n k

theorem readback_apply (n k : Nat) :
    readback n k = BEDC.Derived.RencontresNumberUp.rencontresNumber n k := by
  rfl

private theorem binomialC_eq_nat_choose (n k : Nat) :
    BEDC.Derived.BinomialIdentitiesUp.C n k = Nat.choose n k := by
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

private theorem derangementNumber_eq_numDerangements (n : Nat) :
    BEDC.Derived.DerangementUp.derangementNumber n = numDerangements n := by
  change BedcMathlibBridge.Constructive.Derangement.toNat n = numDerangements n
  exact BedcMathlibBridge.Constructive.Derangement.toNat_eq_numDerangements n

theorem readback_eq_nat_choose_mul_numDerangements (n k : Nat) :
    readback n k = Nat.choose n k * numDerangements (n - k) := by
  unfold readback BEDC.Derived.RencontresNumberUp.rencontresNumber
  unfold BEDC.Derived.RencontresNumberUp.C
  unfold BEDC.Derived.RencontresNumberUp.derangementNumber
  rw [binomialC_eq_nat_choose n k]
  rw [derangementNumber_eq_numDerangements (n - k)]

theorem readback_fixed_all (n : Nat) :
    readback n n = 1 := by
  change BEDC.Derived.RencontresNumberUp.rencontresNumber n n = 1
  exact BEDC.Derived.RencontresNumberUp.rencontresNumber_fixed_all n

theorem readback_fixed_none (n : Nat) :
    readback n 0 = numDerangements n := by
  calc
    readback n 0 = Nat.choose n 0 * numDerangements (n - 0) :=
      readback_eq_nat_choose_mul_numDerangements n 0
    _ = numDerangements n := by
      rw [Nat.choose_zero_right, Nat.sub_zero, Nat.one_mul]

theorem readback_above (n : Nat) :
    readback n (Nat.succ n) = 0 := by
  change BEDC.Derived.RencontresNumberUp.rencontresNumber n (Nat.succ n) = 0
  exact BEDC.Derived.RencontresNumberUp.rencontresNumber_above n

theorem readback_three_one :
    readback 3 1 = 3 := by
  rfl

theorem readback_four_two :
    readback 4 2 = 6 := by
  rfl

end BedcMathlibBridge.Constructive.Rencontres
