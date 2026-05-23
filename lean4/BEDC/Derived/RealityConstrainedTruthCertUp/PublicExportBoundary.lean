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

theorem RealityConstrainedTruthCertPublicExportBoundary [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N classifierRead towerStabilityRead invariantLedgerRead
      failureNameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S K classifierRead →
      Cont T U towerStabilityRead →
        Cont I L invariantLedgerRead →
          Cont F N failureNameRead →
            PkgSig bundle failureNameRead pkg →
              TasteGate.realityConstrainedTruthCertFields
                  (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
                [S, Sigma, K, T, U, D, I, L, F, N] ∧
              Cont S K classifierRead ∧
                Cont T U towerStabilityRead ∧
                  Cont I L invariantLedgerRead ∧
                    Cont F N failureNameRead ∧
                      PkgSig bundle failureNameRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row failureNameRead)
                          (fun row : BHist => hsame row failureNameRead)
                          (fun row : BHist =>
                            hsame row failureNameRead ∧ PkgSig bundle failureNameRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro classifierRoute towerRoute invariantRoute failureRoute failurePkg
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row failureNameRead)
        (fun row : BHist => hsame row failureNameRead)
        (fun row : BHist =>
          hsame row failureNameRead ∧ PkgSig bundle failureNameRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := ⟨failureNameRead, hsame_refl failureNameRead⟩
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
        exact source
      ledger_sound := by
        intro _row source
        exact ⟨source, failurePkg⟩
    }
  exact
    ⟨rfl, classifierRoute, towerRoute, invariantRoute, failureRoute, failurePkg, cert⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
