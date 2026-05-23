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

theorem RealityConstrainedTruthCertMethodologyLedgerHandoff [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N methodologyRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L F methodologyRead ->
      Cont methodologyRead N exportRead ->
        PkgSig bundle exportRead pkg ->
          TasteGate.realityConstrainedTruthCertFields
              (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
            [S, Sigma, K, T, U, D, I, L, F, N] /\
            Cont L F methodologyRead /\
              Cont methodologyRead N exportRead /\
                PkgSig bundle exportRead pkg /\
                  SemanticNameCert
                    (fun row : BHist => hsame row exportRead)
                    (fun row : BHist =>
                      hsame row methodologyRead \/ hsame row exportRead)
                    (fun row : BHist =>
                      hsame row exportRead /\ PkgSig bundle exportRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro methodologyRoute exportRoute exportPkg
  have exportSource :
      (fun row : BHist => hsame row exportRead) exportRead := by
    exact hsame_refl exportRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead)
        (fun row : BHist => hsame row methodologyRead \/ hsame row exportRead)
        (fun row : BHist => hsame row exportRead /\ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead exportSource
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
        exact Or.inr source
      ledger_sound := by
        intro _row source
        exact ⟨source, exportPkg⟩
    }
  exact ⟨rfl, methodologyRoute, exportRoute, exportPkg, cert⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
