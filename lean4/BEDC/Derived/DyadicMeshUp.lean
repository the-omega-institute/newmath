import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Ask
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicMeshUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMeshCarrier [AskSetup] [PackageSetup]
    (level cell interval ledger routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory ledger ∧
    UnaryHistory provenance ∧ UnaryHistory name ∧ Cont level cell interval ∧
      Cont interval ledger routes ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem DyadicMeshCarrier_cell_containment_obligation [AskSetup] [PackageSetup]
    {level cell interval ledger routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshCarrier level cell interval ledger routes provenance name bundle pkg ->
      UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧
        UnaryHistory ledger ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
          UnaryHistory name ∧ Cont level cell interval ∧ Cont interval ledger routes ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  intro carrier
  obtain ⟨levelUnary, cellUnary, ledgerUnary, provenanceUnary, nameUnary, levelCellInterval,
    intervalLedgerRoutes, provenancePkg, namePkg⟩ := carrier
  have intervalUnary : UnaryHistory interval :=
    unary_cont_closed levelUnary cellUnary levelCellInterval
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed intervalUnary ledgerUnary intervalLedgerRoutes
  exact
    ⟨levelUnary, cellUnary, intervalUnary, ledgerUnary, routesUnary, provenanceUnary,
      nameUnary, levelCellInterval, intervalLedgerRoutes, provenancePkg, namePkg⟩

end BEDC.Derived.DyadicMeshUp
