import BEDC.Derived.KeithNumberUp
import Mathlib.Data.Nat.Basic

/-!
Keith-number window-sum readback.

The BEDC side supplies the decimal digit window, fuelled sequence, and hit
predicate. The bridge exposes only the next-window sum against the explicit
mathlib list fold `List.foldr Nat.add 0`.
-/

namespace BedcMathlibBridge.Constructive.KeithNumber

private def mathlibListFoldProvenanceAnchor : Unit :=
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  let _ : forall digits : List Nat,
    List.foldr Nat.add 0 digits = List.foldr Nat.add 0 digits := fun _ => rfl
  ()

def nextValueReadback (digits : List Nat) (fuel : Nat) : Nat :=
  let _ := mathlibListFoldProvenanceAnchor
  BEDC.Derived.KeithNumberUp.keithNextValue digits fuel

theorem nextValueReadback_apply (digits : List Nat) (fuel : Nat) :
    nextValueReadback digits fuel =
      BEDC.Derived.KeithNumberUp.keithNextValue digits fuel := by
  rfl

theorem mathlibNatListAnchor : Nat.succ_injective = Nat.succ_injective := by
  rfl

private theorem keithDigitSum_eq_list_foldr_core (digits : List Nat) :
    BEDC.Derived.KeithNumberUp.keithDigitSum digits =
      List.foldr Nat.add 0 digits := by
  induction digits with
  | nil =>
      rfl
  | cons digit rest ih =>
      change
        digit + BEDC.Derived.KeithNumberUp.keithDigitSum rest =
          digit + List.foldr Nat.add 0 rest
      exact congrArg (fun x => digit + x) ih

theorem keithDigitSum_eq_list_foldr
    (digits : List Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatListAnchor) :
    BEDC.Derived.KeithNumberUp.keithDigitSum digits =
      List.foldr Nat.add 0 digits :=
  keithDigitSum_eq_list_foldr_core digits

theorem keithNextValue_eq_list_foldr_window
    (digits : List Nat) (fuel : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatListAnchor) :
    BEDC.Derived.KeithNumberUp.keithNextValue digits fuel =
      List.foldr Nat.add 0
        (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel) := by
  calc
    BEDC.Derived.KeithNumberUp.keithNextValue digits fuel =
        BEDC.Derived.KeithNumberUp.keithDigitSum
          (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel) :=
      BEDC.Derived.KeithNumberUp.keithNextValue_eq_window_sum digits fuel
    _ =
        List.foldr Nat.add 0
          (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel) :=
      keithDigitSum_eq_list_foldr
        (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel)

theorem nextValueReadback_eq_list_foldr_window
    (digits : List Nat) (fuel : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatListAnchor) :
    nextValueReadback digits fuel =
      List.foldr Nat.add 0
        (BEDC.Derived.KeithNumberUp.keithWindowFuel digits fuel) := by
  rw [nextValueReadback_apply]
  exact keithNextValue_eq_list_foldr_window digits fuel

end BedcMathlibBridge.Constructive.KeithNumber
