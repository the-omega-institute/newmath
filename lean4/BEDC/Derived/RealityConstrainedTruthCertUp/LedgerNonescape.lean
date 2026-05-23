import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertLedgerNonescape [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N ledgerRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TasteGate.realityConstrainedTruthCertFields
        (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
      [S, Sigma, K, T, U, D, I, L, F, N] ->
      Cont I L ledgerRead ->
        Cont L N exportRead ->
          PkgSig bundle exportRead pkg ->
            hsame L L ∧ Cont I L ledgerRead ∧ Cont L N exportRead ∧
              PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame
  intro _fields ledgerRoute exportRoute exportPkg
  exact ⟨hsame_refl L, ledgerRoute, exportRoute, exportPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
