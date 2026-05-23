import BEDC.Derived.LawCertificateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LawCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem LawCertificate_continuation_scope [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N stabilityRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      Cont S E stabilityRead →
        Cont stabilityRead Ld scopedRead →
          PkgSig bundle scopedRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row scopedRead ∧
                  ∃ packet : LawCertificateUp,
                    packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                      lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
              (fun row : BHist => Cont S E stabilityRead ∧ Cont stabilityRead Ld row)
              (fun row : BHist => hsame row scopedRead ∧ PkgSig bundle scopedRead pkg)
              hsame ∧
              Cont S E stabilityRead ∧ Cont stabilityRead Ld scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact stabilityRoute scopedRoute packageScoped
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨scopedRead, hsame_refl scopedRead,
              LawCertificateUp.mk F P C S E Ld H R Q N, rfl, fieldsExact⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨stabilityRoute,
            cont_result_hsame_transport scopedRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, packageScoped⟩
    }
  · exact ⟨stabilityRoute, scopedRoute⟩

end BEDC.Derived.LawCertificateUp
