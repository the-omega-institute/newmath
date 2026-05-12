import BEDC.HostBridge.HostInterpreter
import BEDC.HostBridge.ChurchNatRoundTrip
import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.MetaCIC.TypedExamples.ChurchNatArith
import BEDC.MetaCIC.Normalization

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_mul : Term :=
  BEDC.MetaCIC.church_mul

abbrev churchAddApp (m n : Nat) : Term :=
  Term.app (Term.app church_add (hostNatToChurch m)) (hostNatToChurch n)

abbrev churchMulApp (m n : Nat) : Term :=
  Term.app (Term.app church_mul (hostNatToChurch m)) (hostNatToChurch n)

def churchSuccFuel (n : Nat) : Nat :=
  1000 + (n + 1) * 10

theorem interpret_church_succ_at_fuel (n : Nat) :
    interpretClosedNat (churchSuccFuel n)
      (Term.app church_succ (hostNatToChurch n)) = some (n + 1) := by
  change
    interpretClosedNat (1000 + (n + 1) * 10)
      (hostNatToChurch (n + 1)) = some (n + 1)
  unfold interpretClosedNat
  rw [hostNat_roundtrip_identity (n + 1)]

theorem interpret_church_succ (n : Nat) :
    ∃ fuel, interpretClosedNat fuel
      (Term.app church_succ (hostNatToChurch n)) = some (n + 1) := by
  exact Exists.intro (churchSuccFuel n) (interpret_church_succ_at_fuel n)

theorem interpret_church_add_two_three_at_fuel :
    interpretClosedNat 50 (churchAddApp 2 3) = some (2 + 3) := by
  rfl

theorem interpret_church_add_two_three :
    ∃ fuel, interpretClosedNat fuel (churchAddApp 2 3) = some (2 + 3) := by
  exact Exists.intro 50 interpret_church_add_two_three_at_fuel

theorem interpret_church_add_zero_zero_at_fuel :
    interpretClosedNat 20 (churchAddApp 0 0) = some (0 + 0) := by
  rfl

theorem interpret_church_add_zero_one_at_fuel :
    interpretClosedNat 30 (churchAddApp 0 1) = some (0 + 1) := by
  rfl

theorem interpret_church_add_one_zero_at_fuel :
    interpretClosedNat 30 (churchAddApp 1 0) = some (1 + 0) := by
  rfl

theorem interpret_church_add_one_one_at_fuel :
    interpretClosedNat 40 (churchAddApp 1 1) = some (1 + 1) := by
  rfl

theorem interpret_church_add_one_two_at_fuel :
    interpretClosedNat 50 (churchAddApp 1 2) = some (1 + 2) := by
  rfl

theorem interpret_church_add_two_one_at_fuel :
    interpretClosedNat 50 (churchAddApp 2 1) = some (2 + 1) := by
  rfl

theorem interpret_church_add_two_two_at_fuel :
    interpretClosedNat 60 (churchAddApp 2 2) = some (2 + 2) := by
  rfl

theorem interpret_church_add_three_two_at_fuel :
    interpretClosedNat 70 (churchAddApp 3 2) = some (3 + 2) := by
  rfl

theorem interpret_church_add_three_four_at_fuel :
    interpretClosedNat 100 (churchAddApp 3 4) = some (3 + 4) := by
  rfl

theorem interpret_church_mul_three_four_at_fuel :
    interpretClosedNat 100 (churchMulApp 3 4) = some (3 * 4) := by
  rfl

theorem interpret_church_mul_three_four :
    ∃ fuel, interpretClosedNat fuel (churchMulApp 3 4) = some (3 * 4) := by
  exact Exists.intro 100 interpret_church_mul_three_four_at_fuel

theorem interpret_church_mul_zero_zero_at_fuel :
    interpretClosedNat 30 (churchMulApp 0 0) = some (0 * 0) := by
  rfl

theorem interpret_church_mul_zero_three_at_fuel :
    interpretClosedNat 50 (churchMulApp 0 3) = some (0 * 3) := by
  rfl

theorem interpret_church_mul_three_zero_at_fuel :
    interpretClosedNat 50 (churchMulApp 3 0) = some (3 * 0) := by
  rfl

theorem interpret_church_mul_one_one_at_fuel :
    interpretClosedNat 50 (churchMulApp 1 1) = some (1 * 1) := by
  rfl

theorem interpret_church_mul_one_four_at_fuel :
    interpretClosedNat 80 (churchMulApp 1 4) = some (1 * 4) := by
  rfl

theorem interpret_church_mul_two_two_at_fuel :
    interpretClosedNat 70 (churchMulApp 2 2) = some (2 * 2) := by
  rfl

theorem interpret_church_mul_two_three_at_fuel :
    interpretClosedNat 90 (churchMulApp 2 3) = some (2 * 3) := by
  rfl

theorem interpret_church_mul_four_two_at_fuel :
    interpretClosedNat 100 (churchMulApp 4 2) = some (4 * 2) := by
  rfl

example :
    interpretClosedNat 50
      (Term.app (Term.app church_add (hostNatToChurch 2)) (hostNatToChurch 3))
    = some 5 := by
  rfl

example :
    interpretClosedNat 100
      (Term.app (Term.app church_mul (hostNatToChurch 3)) (hostNatToChurch 4))
    = some 12 := by
  rfl

example :
    interpretClosedNat (churchSuccFuel 7)
      (Term.app church_succ (hostNatToChurch 7)) = some 8 := by
  exact interpret_church_succ_at_fuel 7

end BEDC.HostBridge
