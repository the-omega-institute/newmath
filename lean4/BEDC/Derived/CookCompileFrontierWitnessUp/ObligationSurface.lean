import BEDC.Derived.CookCompileFrontierWitnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CookCompileFrontierWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CookCompileFrontierWitnessCarrier [AskSetup] [PackageSetup]
    (stage coordinate audit obstruction transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory stage ∧ UnaryHistory coordinate ∧ UnaryHistory audit ∧
    UnaryHistory obstruction ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem CookCompileFrontierWitnessObligationSurface [AskSetup] [PackageSetup]
    {stage coordinate audit obstruction transport route provenance name stageRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CookCompileFrontierWitnessCarrier stage coordinate audit obstruction transport route
        provenance name bundle pkg →
      Cont stage audit stageRead →
      Cont stageRead coordinate auditRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle name pkg →
      UnaryHistory stageRead ∧ UnaryHistory auditRead ∧ Cont stage audit stageRead ∧
        Cont stageRead coordinate auditRead ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: CookCompileFrontierWitnessCarrier BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier stageAudit stageReadCoordinate provenancePkg namePkg
  obtain ⟨stageUnary, coordinateUnary, auditUnary, _obstructionUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, _carrierProvenancePkg, _carrierNamePkg⟩ :=
    carrier
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed stageUnary auditUnary stageAudit
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed stageReadUnary coordinateUnary stageReadCoordinate
  exact
    ⟨stageReadUnary, auditReadUnary, stageAudit, stageReadCoordinate, provenancePkg,
      namePkg⟩

end BEDC.Derived.CookCompileFrontierWitnessUp
