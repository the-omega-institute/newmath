import BedcMathlibBridge.Constructive.CentralBinom

namespace BedcMathlibBridge.Export.CentralBinom

open BedcMathlibBridge.Constructive.CentralBinom
open BEDC.Derived.LucasTheoremUp

structure CentralBinomExportWitness where
  readback : Nat -> Nat
  readback_apply : ∀ n : Nat, readback n = toNat n
  bedc_apply : ∀ n : Nat, readback n = bedcChooseNat (2 * n) n
  centralBinom_apply : ∀ n : Nat, readback n = Nat.centralBinom n

def centralBinomExport : CentralBinomExportWitness where
  readback := toNat
  readback_apply := by
    intro n
    rfl
  bedc_apply := toNat_apply
  centralBinom_apply := toNat_eq_centralBinom

theorem bedcChooseNat_central_eq_centralBinom (n : Nat) :
    bedcChooseNat (2 * n) n = Nat.centralBinom n :=
  (BedcMathlibBridge.Constructive.CentralBinom.toNat_apply n).symm.trans
    (BedcMathlibBridge.Constructive.CentralBinom.toNat_eq_centralBinom n)

end BedcMathlibBridge.Export.CentralBinom
