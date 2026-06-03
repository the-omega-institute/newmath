import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived

inductive RealDecimalNormalFormUp : Type
  | carrier

namespace RealDecimalNormalFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RealDecimalNormalFormCarrier (S T R D W H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg NameCert
  Cont S T R ∧ Cont R D W ∧ hsame H C ∧ hsame P N

theorem RealDecimalNormalFormCarrier_namecert_obligation_surface
    {S T R D W H C P N : BHist}
    (carrier : RealDecimalNormalFormCarrier S T R D W H C P N) :
    Cont S T R ∧
      SemanticNameCert
        (fun row : BHist => RealDecimalNormalFormCarrier S T R D W H C P row)
        (fun row : BHist => RealDecimalNormalFormCarrier S T R D W H C P row)
        (fun row : BHist => RealDecimalNormalFormCarrier S T R D W H C P row)
        (fun h k : BHist => hsame h k) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert Pkg NameCert
  obtain ⟨sourceRoute, handoffRoute, transportRow, nameRow⟩ := carrier
  have sourceN : RealDecimalNormalFormCarrier S T R D W H C P N :=
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

end RealDecimalNormalFormUp
end BEDC.Derived
