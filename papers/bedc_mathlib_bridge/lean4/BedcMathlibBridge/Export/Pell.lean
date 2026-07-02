import BedcMathlibBridge.Constructive.Pell

/-!
Export witness for the Pell recurrence readback correspondence.

The witness records the BEDC `pellPairMul` readback for the special
Matiyasevic parameters `D = a^2 - 1`, base pair `(a,1)`, and its exact
agreement with mathlib's recursive `Pell.xz` and `Pell.yz` sequences.
-/

namespace BedcMathlibBridge.Export.Pell

open BedcMathlibBridge.Constructive.Pell

structure PellRecurrenceExportWitness where
  xReadback : Nat -> Nat -> Int
  yReadback : Nat -> Nat -> Int
  x_apply : ∀ a n : Nat, xReadback a n = bedcX a n
  y_apply : ∀ a n : Nat, yReadback a n = bedcY a n
  x_zero : ∀ a : Nat, xReadback a 0 = 1
  y_zero : ∀ a : Nat, yReadback a 0 = 0
  x_succ : ∀ a n : Nat,
    xReadback a (n + 1) =
      xReadback a n * (a : Int) + ((a * a - 1 : Nat) : Int) * yReadback a n
  y_succ : ∀ a n : Nat,
    yReadback a (n + 1) = xReadback a n + yReadback a n * (a : Int)
  mathlib_xz : ∀ {a : Nat} (a1 : 1 < a) (n : Nat),
    xReadback a n = _root_.Pell.xz a1 n
  mathlib_yz : ∀ {a : Nat} (a1 : 1 < a) (n : Nat),
    yReadback a n = _root_.Pell.yz a1 n

def pellRecurrenceExport : PellRecurrenceExportWitness where
  xReadback := bedcX
  yReadback := bedcY
  x_apply := by
    intro a n
    rfl
  y_apply := by
    intro a n
    rfl
  x_zero := bedcX_zero
  y_zero := bedcY_zero
  x_succ := bedcX_succ
  y_succ := bedcY_succ
  mathlib_xz := bedcX_eq_mathlib_xz
  mathlib_yz := bedcY_eq_mathlib_yz

theorem pell_xy_readback {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcX a n = _root_.Pell.xz a1 n ∧
      bedcY a n = _root_.Pell.yz a1 n :=
  BedcMathlibBridge.Constructive.Pell.readback_eq_mathlib a1 n

theorem pell_xz_readback {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcX a n = _root_.Pell.xz a1 n :=
  (pell_xy_readback a1 n).left

theorem pell_yz_readback {a : Nat} (a1 : 1 < a) (n : Nat) :
    bedcY a n = _root_.Pell.yz a1 n :=
  (pell_xy_readback a1 n).right

end BedcMathlibBridge.Export.Pell
