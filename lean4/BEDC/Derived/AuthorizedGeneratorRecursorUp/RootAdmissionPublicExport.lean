import BEDC.Derived.AuthorizedGeneratorRecursorUp.AdmissionExhaustion
import BEDC.Derived.AuthorizedGeneratorRecursorUp.AdmissionExhaustionStrictObstruction
import BEDC.Derived.AuthorizedGeneratorRecursorUp.DownstreamNameCertPackage
import BEDC.Derived.AuthorizedGeneratorRecursorUp.RouteRefusal

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem AuthorizedGeneratorRecursorRootAdmissionPublicExport [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead refusalRead boundaryRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E M ->
        Cont M B D ->
          Cont D O A ->
            Cont O A rootRead ->
              Cont G N refusalRead ->
                Cont refusalRead A boundaryRead ->
                  Cont boundaryRead N terminalRead ->
                    PkgSig bundle terminalRead pkg ->
                      SemanticNameCert
                        (fun row : BHist => hsame row terminalRead)
                        (fun row : BHist =>
                          Cont I E M ∧ Cont M B D ∧ Cont D O A ∧
                            hsame row terminalRead)
                        (fun row : BHist =>
                          PkgSig bundle terminalRead pkg ∧ hsame row terminalRead)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier carrierIEM carrierMBD carrierDOA outputRoot refusalRoute boundaryRoute
    terminalRoute terminalPkg
  exact {
    core := {
      carrier_inhabited := Exists.intro terminalRead (hsame_refl terminalRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact ⟨carrierIEM, carrierMBD, carrierDOA, source⟩
    ledger_sound := by
      intro _row source
      exact ⟨terminalPkg, source⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
