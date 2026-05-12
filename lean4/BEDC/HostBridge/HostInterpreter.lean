import BEDC.MetaCIC.TypedExamples.ChurchNatRec
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.MetaCIC.Normalization
import BEDC.HostBridge.MetaCICTransport
import BEDC.HostBridge.ChurchNatRoundTrip

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_add : Term :=
  BEDC.MetaCIC.ChurchNatRec.church_add

abbrev hostNat2 : Term :=
  hostNatToChurch 2

abbrev hostNat3 : Term :=
  hostNatToChurch 3

def interpretClosedNat (fuel : Nat) (t : Term) : Option Nat :=
  some (churchToHostNat t fuel)

theorem interpretClosedNat_roundtrip (n : Nat) :
    ∃ fuel, interpretClosedNat fuel (hostNatToChurch n) = some n := by
  exact
    Exists.intro (1000 + n * 10)
      (by
        unfold interpretClosedNat
        rw [hostNat_roundtrip_identity n])

theorem interpretClosedNat_value (fuel : Nat) (t : Term) :
    interpretClosedNat fuel t = some (churchToHostNat t fuel) := by
  rfl

theorem interpretClosedNat_spine_roundtrip (n fuel : Nat) :
    interpretClosedNat (fuel + n) (hostNatToChurch n) = some n := by
  unfold interpretClosedNat
  unfold churchToHostNat
  exact congrArg some (churchSuccSpineToHostNat_identity n fuel)

example : interpretClosedNat 5 church_zero = some 0 := by
  exact interpretClosedNat_spine_roundtrip 0 5

example : interpretClosedNat 5 (Term.app church_succ church_zero) = some 1 := by
  exact interpretClosedNat_spine_roundtrip 1 4

example :
    interpretClosedNat 10
      (Term.app church_succ (Term.app church_succ church_zero)) = some 2 := by
  exact interpretClosedNat_spine_roundtrip 2 8

example :
    interpretClosedNat 50 (Term.app (Term.app church_add hostNat2) hostNat3) =
      some 5 := by
  rfl

end BEDC.HostBridge
