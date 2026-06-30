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

theorem LawCertificateCarrier_admission [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N sourceRead stabilityRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] ->
      Cont F P sourceRead ->
        Cont S E stabilityRead ->
          Cont stabilityRead Ld ledgerRead ->
            Cont H R Q ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row ledgerRead ∧
                        ∃ packet : LawCertificateUp,
                          packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                            lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
                    (fun row : BHist =>
                      hsame row ledgerRead ∧ Cont F P sourceRead ∧
                        Cont S E stabilityRead ∧ Cont stabilityRead Ld ledgerRead)
                    (fun row : BHist =>
                      hsame row ledgerRead ∧ Cont H R Q ∧ PkgSig bundle N pkg)
                    hsame ∧
                  lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
                    [F, P, C, S, E, Ld, H, R, Q, N] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact sourceRoute stabilityRoute ledgerRoute replayRoute packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨ledgerRead, hsame_refl ledgerRead,
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
        exact ⟨source.left, sourceRoute, stabilityRoute, ledgerRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, replayRoute, packageName⟩
    }
  · exact fieldsExact

end BEDC.Derived.LawCertificateUp
