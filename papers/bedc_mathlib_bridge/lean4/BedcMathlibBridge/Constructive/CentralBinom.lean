import BEDC.Derived.LucasTheoremUp
import BedcMathlibBridge.Constructive.Binomial
import Mathlib.Data.Nat.Choose.Central

namespace BedcMathlibBridge.Constructive.CentralBinom

open BEDC.Derived.LucasTheoremUp

private def mathlibCentralBinomProvenanceAnchor : Unit :=
  let _ : ∀ n : Nat, Nat.centralBinom n = Nat.centralBinom n :=
    fun _ => rfl
  ()

/-- The BEDC central binomial coefficient reads back the `Pascal`-recursive
`bedcChooseNat` at the central index `(2n, n)`. -/
def toNat (n : Nat) : Nat :=
  let _ := mathlibCentralBinomProvenanceAnchor
  bedcChooseNat (2 * n) n

theorem toNat_apply (n : Nat) : toNat n = bedcChooseNat (2 * n) n := by
  rfl

/-- The BEDC readback of the central binomial coefficient agrees with mathlib's
`Nat.centralBinom`, which is `(2n).choose n`. The correspondence reuses the
already-certified `bedcChooseNat n k = Nat.choose n k` equality. -/
theorem toNat_eq_centralBinom (n : Nat) :
    toNat n = Nat.centralBinom n := by
  rw [toNat_apply, BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose,
    Nat.centralBinom_eq_two_mul_choose]

end BedcMathlibBridge.Constructive.CentralBinom
