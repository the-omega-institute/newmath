import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicMeshUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicMeshPacket [AskSetup] [PackageSetup]
    (level cell interval endpoint radius order transport refinement provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧ UnaryHistory endpoint ∧
    UnaryHistory radius ∧ UnaryHistory order ∧ UnaryHistory transport ∧
      UnaryHistory refinement ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont level cell interval ∧ Cont interval endpoint radius ∧
          PkgSig bundle provenance pkg

theorem DyadicMeshPacket_cell_containment_obligation [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert containment :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint containment ->
        PkgSig bundle containment pkg ->
          UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧
            UnaryHistory endpoint ∧ UnaryHistory radius ∧ UnaryHistory order ∧
              UnaryHistory transport ∧ UnaryHistory refinement ∧ UnaryHistory provenance ∧
                UnaryHistory nameCert ∧ UnaryHistory containment ∧ Cont level cell interval ∧
                  Cont interval endpoint radius ∧ Cont interval endpoint containment ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle containment pkg := by
  intro packet intervalEndpointContainment containmentPkg
  rcases packet with
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, radiusUnary, orderUnary,
      transportUnary, refinementUnary, provenanceUnary, nameCertUnary, levelCellInterval,
      intervalEndpointRadius, provenancePkg⟩
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointContainment
  exact
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, radiusUnary, orderUnary,
      transportUnary, refinementUnary, provenanceUnary, nameCertUnary, containmentUnary,
      levelCellInterval, intervalEndpointRadius, intervalEndpointContainment, provenancePkg,
      containmentPkg⟩

end BEDC.Derived.DyadicMeshUp
