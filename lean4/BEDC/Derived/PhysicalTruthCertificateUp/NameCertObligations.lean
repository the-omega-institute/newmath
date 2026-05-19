import BEDC.Derived.PhysicalTruthCertificateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalTruthCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PhysicalTruthCertificateNameCertObligations
    {S F O D I L R H C P N endpoint : BHist} :
    PhysicalTruthCertificateUp →
      UnaryHistory endpoint →
        Cont S F R →
          Cont R I endpoint →
            SemanticNameCert
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist => hsame row endpoint ∧ Cont S F R)
              (fun row : BHist => hsame row endpoint ∧ Cont R I endpoint)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier endpointUnary sfr rie
  cases carrier with
  | mk _S _F _O _D _I _L _R _H _C _P _N =>
      exact {
        core := {
          carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
            intro _row _other sameRows source
            exact
              ⟨hsame_trans (hsame_symm sameRows) source.left,
                unary_transport source.right sameRows⟩
        }
        pattern_sound := by
          intro _row source
          exact ⟨source.left, sfr⟩
        ledger_sound := by
          intro _row source
          exact ⟨source.left, rie⟩
      }

end BEDC.Derived.PhysicalTruthCertificateUp
