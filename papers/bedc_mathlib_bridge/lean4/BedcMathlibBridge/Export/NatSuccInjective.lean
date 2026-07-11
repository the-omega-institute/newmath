import BedcMathlibBridge.Constructive.NatSuccInjective

namespace BedcMathlibBridge.Export.NatSuccInjective

open BedcMathlibBridge.Constructive.NatSuccInjective

structure NatSuccInjectiveExportWitness where
  readback : Function.Injective Nat.succ
  readback_apply : readback = succInjectiveReadback
  mathlib_apply : readback = Nat.succ_injective

def natSuccInjectiveExport : NatSuccInjectiveExportWitness where
  readback := succInjectiveReadback
  readback_apply := by
    rfl
  mathlib_apply := succInjectiveReadback_eq_nat_succ_injective

theorem nat_succ_injective_mathlib_correspondence :
    succInjectiveReadback = Nat.succ_injective := by
  exact succInjectiveReadback_eq_nat_succ_injective

end BedcMathlibBridge.Export.NatSuccInjective
