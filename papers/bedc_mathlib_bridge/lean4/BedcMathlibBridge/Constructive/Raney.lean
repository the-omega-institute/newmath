import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.RaneyNumberUp
import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.Raney

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def toNat (m r n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.RaneyNumberUp.raneyNumber m r n

theorem toNat_apply (m r n : Nat) :
    toNat m r n = BEDC.Derived.RaneyNumberUp.raneyNumber m r n := by
  rfl

theorem toNat_eq_nat_choose_formula (m r n : Nat) :
    toNat m r n = r * Nat.choose (m * n + r) n / (m * n + r) := by
  have choose_readback :
      BEDC.Derived.RaneyNumberUp.C (m * n + r) n =
        Nat.choose (m * n + r) n := by
    change BEDC.Derived.LucasTheoremUp.bedcChooseNat (m * n + r) n =
      Nat.choose (m * n + r) n
    exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose
      (m * n + r) n
  calc
    toNat m r n = BEDC.Derived.RaneyNumberUp.raneyNumber m r n := rfl
    _ =
        r * BEDC.Derived.RaneyNumberUp.C (m * n + r) n /
          (m * n + r) :=
      BEDC.Derived.RaneyNumberUp.raney_formula_surface m r n
    _ = r * Nat.choose (m * n + r) n / (m * n + r) := by
      rw [choose_readback]

end BedcMathlibBridge.Constructive.Raney
