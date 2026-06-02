import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived

inductive RegularRealCauchySelectorUp : Type
  | carrier

namespace RegularRealCauchySelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RegularRealCauchySelectorCarrier (R0 M D W Q E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg NameCert
  Cont R0 M D ∧ Cont D W Q ∧ hsame Q E ∧ hsame H C ∧ hsame P N

theorem RegularRealCauchySelectorCarrier_namecert_obligation_surface
    {R0 M D W Q E H C P N : BHist}
    (carrier : RegularRealCauchySelectorCarrier R0 M D W Q E H C P N) :
    Cont R0 M D ∧ Cont D W Q ∧
      SemanticNameCert
        (fun row : BHist => RegularRealCauchySelectorCarrier R0 M D W Q E H C P row)
        (fun row : BHist => RegularRealCauchySelectorCarrier R0 M D W Q E H C P row)
        (fun row : BHist => RegularRealCauchySelectorCarrier R0 M D W Q E H C P row)
        (fun h k : BHist => hsame h k) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert Pkg NameCert
  obtain ⟨sourceRoute, windowRoute, sealRow, transportRow, nameRow⟩ := carrier
  have sourceN : RegularRealCauchySelectorCarrier R0 M D W Q E H C P N :=
    ⟨sourceRoute, windowRoute, sealRow, transportRow, nameRow⟩
  constructor
  · exact sourceRoute
  · constructor
    · exact windowRoute
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
            obtain ⟨sourceRoute', windowRoute', sealRow', transportRow', nameRow'⟩ :=
              sourceRow
            exact
              ⟨sourceRoute', windowRoute', sealRow', transportRow',
                hsame_trans nameRow' sameRows⟩
        }
        pattern_sound := by
          intro _row sourceRow
          exact sourceRow
        ledger_sound := by
          intro _row sourceRow
          exact sourceRow
      }

end RegularRealCauchySelectorUp
end BEDC.Derived
