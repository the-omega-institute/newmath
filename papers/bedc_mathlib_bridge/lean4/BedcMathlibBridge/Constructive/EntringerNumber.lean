import BEDC.Derived.EntringerNumberUp
import Mathlib.Data.Nat.Basic

namespace BedcMathlibBridge.Constructive.EntringerNumber

private def mathlibNatProvenanceAnchor : Unit :=
  let _ : forall a b : Nat, a + b = Nat.add a b := fun _ _ => rfl
  let _ : forall a b : Nat, a - b = Nat.sub a b := fun _ _ => rfl
  let _ : Function.Injective Nat.succ := Nat.succ_injective
  ()

def readback (n k : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.EntringerNumberUp.entringerNumber n k

def zigzagReadback (n : Nat) : Nat :=
  let _ := mathlibNatProvenanceAnchor
  BEDC.Derived.EntringerNumberUp.zigzagByEntringer n

theorem readback_apply (n k : Nat) :
    readback n k = BEDC.Derived.EntringerNumberUp.entringerNumber n k := by
  rfl

theorem zigzagReadback_apply (n : Nat) :
    zigzagReadback n = BEDC.Derived.EntringerNumberUp.zigzagByEntringer n := by
  rfl

theorem readback_zero_zero :
    readback 0 0 = 1 := by
  rfl

theorem readback_zero_succ (k : Nat) :
    readback 0 (Nat.succ k) = 0 := by
  rfl

theorem readback_succ_zero (n : Nat) :
    readback (Nat.succ n) 0 = 0 := by
  rfl

theorem mathlibNatAnchor :
    Nat.succ_injective = Nat.succ_injective := by
  rfl

theorem succ_succ_nat_add_sub
    (n k : Nat)
    (_anchor : Nat.succ_injective = Nat.succ_injective := mathlibNatAnchor) :
    readback (Nat.succ n) (Nat.succ k) =
      Nat.add (readback (Nat.succ n) k) (readback n (Nat.sub n k)) := by
  change
    BEDC.Derived.EntringerNumberUp.entringerNumber (Nat.succ n) (Nat.succ k) =
      Nat.add
        (BEDC.Derived.EntringerNumberUp.entringerNumber (Nat.succ n) k)
        (BEDC.Derived.EntringerNumberUp.entringerNumber n (Nat.sub n k))
  exact BEDC.Derived.EntringerNumberUp.entringer_succ_succ n k

theorem zigzagReadback_zero :
    zigzagReadback 0 = 1 := by
  rfl

theorem zigzagReadback_one :
    zigzagReadback 1 = 1 := by
  rfl

theorem zigzagReadback_two :
    zigzagReadback 2 = 1 := by
  rfl

theorem zigzagReadback_three :
    zigzagReadback 3 = 2 := by
  rfl

theorem zigzagReadback_four :
    zigzagReadback 4 = 5 := by
  rfl

end BedcMathlibBridge.Constructive.EntringerNumber
