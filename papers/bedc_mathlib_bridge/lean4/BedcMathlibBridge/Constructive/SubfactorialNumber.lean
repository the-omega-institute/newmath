import BedcMathlibBridge.Constructive.Derangement
import BEDC.Derived.DerangementUp

/-!
Subfactorial-number readback correspondence.

The BEDC side names the subfactorial surface as an alias of its derangement
counter. The bridge keeps the exported anchor on `subfactorialNumber` while
using the derangement recurrence correspondence to mathlib.
-/

namespace BedcMathlibBridge.Constructive.SubfactorialNumber

private def mathlibNumDerangementsProvenanceAnchor : Unit :=
  let _ : forall n : Nat, numDerangements n = numDerangements n :=
    fun _ => rfl
  ()

def toNat (n : Nat) : Nat :=
  let _ := mathlibNumDerangementsProvenanceAnchor
  BEDC.Derived.DerangementUp.subfactorialNumber n

theorem toNat_apply (n : Nat) :
    toNat n = BEDC.Derived.DerangementUp.subfactorialNumber n := by
  rfl

theorem toNat_zero :
    toNat 0 = 1 := by
  rfl

theorem toNat_one :
    toNat 1 = 0 := by
  rfl

theorem toNat_two_step_recurrence (n : Nat) :
    toNat (n + 2) = (n + 1) * (toNat (n + 1) + toNat n) := by
  exact BEDC.Derived.DerangementUp.subfactorialNumber_two_step_recurrence n

theorem toNat_eq_derangementNumber (n : Nat) :
    toNat n = BEDC.Derived.DerangementUp.derangementNumber n := by
  rfl

theorem toNat_eq_numDerangements (n : Nat) :
    toNat n = numDerangements n := by
  change BedcMathlibBridge.Constructive.Derangement.toNat n = numDerangements n
  exact BedcMathlibBridge.Constructive.Derangement.toNat_eq_numDerangements n

theorem subfactorialNumber_eq_numDerangements (n : Nat) :
    BEDC.Derived.DerangementUp.subfactorialNumber n = numDerangements n := by
  exact (toNat_apply n).symm.trans (toNat_eq_numDerangements n)

end BedcMathlibBridge.Constructive.SubfactorialNumber
