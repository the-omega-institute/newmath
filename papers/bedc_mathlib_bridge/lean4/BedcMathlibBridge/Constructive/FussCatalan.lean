import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.FussCatalanUp
import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.FussCatalan

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def toNat (m n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.FussCatalanUp.fussCatalanCount m n

theorem toNat_apply (m n : Nat) :
    toNat m n = BEDC.Derived.FussCatalanUp.fussCatalanCount m n := by
  rfl

theorem toNat_eq_nat_choose_formula (m n : Nat) :
    toNat m n =
      Nat.choose (m * n) n / ((m - 1) * n + 1) := by
  have choose_readback :
      BEDC.Derived.FussCatalanUp.C (m * n) n =
        Nat.choose (m * n) n := by
    change BEDC.Derived.LucasTheoremUp.bedcChooseNat (m * n) n =
      Nat.choose (m * n) n
    exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose
      (m * n) n
  calc
    toNat m n = BEDC.Derived.FussCatalanUp.fussCatalanCount m n := rfl
    _ =
        BEDC.Derived.FussCatalanUp.fussCatalanNumerator m n /
          BEDC.Derived.FussCatalanUp.fussCatalanDenom m n := by
      rfl
    _ =
        BEDC.Derived.FussCatalanUp.C (m * n) n /
          ((m - 1) * n + 1) := by
      rfl
    _ = Nat.choose (m * n) n / ((m - 1) * n + 1) := by
      rw [choose_readback]

theorem toNat_prompt_shift (m n : Nat) :
    toNat (Nat.succ m) n =
      BEDC.Derived.FussCatalanUp.fussCatalanPromptCount m n := by
  exact (BEDC.Derived.FussCatalanUp.fussCatalanPrompt_shift m n).symm

end BedcMathlibBridge.Constructive.FussCatalan
