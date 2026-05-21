import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertExportDefeatExhaustion [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N failureName exportDefeat terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F N failureName ->
      Cont failureName L exportDefeat ->
        Cont exportDefeat N terminalRead ->
          PkgSig bundle terminalRead pkg ->
            TasteGate.realityConstrainedTruthCertFields
                (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
              [S, Sigma, K, T, U, D, I, L, F, N] /\
              Cont F N failureName /\
                Cont failureName L exportDefeat /\
                  Cont exportDefeat N terminalRead /\
                    PkgSig bundle terminalRead pkg /\
                      SemanticNameCert
                        (fun row : BHist => hsame row terminalRead)
                        (fun row : BHist =>
                          hsame row failureName \/ hsame row exportDefeat \/
                            hsame row terminalRead)
                        (fun row : BHist =>
                          hsame row terminalRead /\ PkgSig bundle terminalRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro failureRoute defeatRoute terminalRoute terminalPkg
  have terminalSource :
      (fun row : BHist => hsame row terminalRead) terminalRead := by
    exact hsame_refl terminalRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead)
        (fun row : BHist =>
          hsame row failureName \/ hsame row exportDefeat \/ hsame row terminalRead)
        (fun row : BHist => hsame row terminalRead /\ PkgSig bundle terminalRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro terminalRead terminalSource
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source)
      ledger_sound := by
        intro _row source
        exact ⟨source, terminalPkg⟩
    }
  exact ⟨rfl, failureRoute, defeatRoute, terminalRoute, terminalPkg, cert⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
