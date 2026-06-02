import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived

inductive RealReciprocalUp : Type
  | carrier

namespace RealReciprocalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RealReciprocalCarrier (R A D M H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg NameCert
  Cont R A D ∧ Cont D M H ∧ hsame C P ∧ hsame P N

theorem RealReciprocalCarrier_namecert_obligation_surface
    {R A D M H C P N : BHist}
    (carrier : RealReciprocalCarrier R A D M H C P N) :
    Cont R A D ∧
      SemanticNameCert
        (fun row : BHist => RealReciprocalCarrier R A D M H C P row)
        (fun row : BHist => RealReciprocalCarrier R A D M H C P row)
        (fun row : BHist => RealReciprocalCarrier R A D M H C P row)
        (fun h k : BHist => hsame h k) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert Pkg NameCert
  obtain ⟨sourceRoute, handoffRoute, transportRow, nameRow⟩ := carrier
  have sourceN : RealReciprocalCarrier R A D M H C P N :=
    ⟨sourceRoute, handoffRoute, transportRow, nameRow⟩
  constructor
  · exact sourceRoute
  · exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          obtain ⟨sourceRoute', handoffRoute', transportRow', nameRow'⟩ := sourceRow
          exact
            ⟨sourceRoute', handoffRoute', transportRow',
              hsame_trans nameRow' sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow
      ledger_sound := by
        intro _row sourceRow
        exact sourceRow
    }

end RealReciprocalUp
end BEDC.Derived
