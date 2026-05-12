import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicMeshUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicMeshPacket_public_export_boundary [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert
      containment handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint containment ->
        Cont containment provenance handoff ->
          PkgSig bundle containment pkg ->
            PkgSig bundle handoff pkg ->
              UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧
                UnaryHistory containment ∧ UnaryHistory handoff ∧ Cont level cell interval ∧
                  Cont interval endpoint containment ∧ Cont containment provenance handoff ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle containment pkg ∧
                      PkgSig bundle handoff pkg := by
  intro packet intervalEndpointContainment containmentProvenanceHandoff containmentPkg handoffPkg
  rcases packet with
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      _transportUnary, _refinementUnary, provenanceUnary, _nameCertUnary, levelCellInterval,
      _intervalEndpointRadius, provenancePkg⟩
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointContainment
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed containmentUnary provenanceUnary containmentProvenanceHandoff
  exact
    ⟨levelUnary, cellUnary, intervalUnary, containmentUnary, handoffUnary, levelCellInterval,
      intervalEndpointContainment, containmentProvenanceHandoff, provenancePkg, containmentPkg,
      handoffPkg⟩

theorem DyadicMeshPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance name
      containment : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory level ->
      UnaryHistory cell ->
        UnaryHistory interval ->
          UnaryHistory endpoint ->
            UnaryHistory radius ->
              UnaryHistory order ->
                UnaryHistory transport ->
                  UnaryHistory refinement ->
                    UnaryHistory provenance ->
                      UnaryHistory name ->
                        Cont level cell interval ->
                          Cont interval endpoint radius ->
                            Cont interval endpoint containment ->
                              PkgSig bundle provenance pkg ->
                                PkgSig bundle containment pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row containment ∧ UnaryHistory row ∧
                                        PkgSig bundle row pkg)
                                    (fun row : BHist =>
                                      UnaryHistory level ∧ UnaryHistory cell ∧
                                        UnaryHistory interval ∧ Cont interval endpoint row)
                                    (fun row : BHist =>
                                      PkgSig bundle row pkg ∧ Cont level cell interval)
                                    (fun row row' : BHist =>
                                      PkgSig bundle row pkg ∧ hsame row row') := by
  intro levelUnary cellUnary intervalUnary endpointUnary _radiusUnary _orderUnary
  intro _transportUnary _refinementUnary _provenanceUnary _nameUnary
  intro levelCellInterval _intervalEndpointRadius intervalEndpointContainment
  intro _provenancePkg containmentPkg
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointContainment
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro containment ⟨hsame_refl containment, containmentUnary, containmentPkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨sourceRow.right.right, hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        cases classified.right
        exact ⟨classified.left, hsame_refl _⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left,
          hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨levelUnary, cellUnary, intervalUnary, intervalEndpointContainment⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, levelCellInterval⟩
  }

theorem DyadicMeshPacket_refinement_stability [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert level' cell'
      interval' endpoint' radius' order' transport' refinement' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      hsame level level' ->
        hsame cell cell' ->
          hsame endpoint endpoint' ->
            hsame radius radius' ->
              hsame order order' ->
                hsame transport transport' ->
                  hsame refinement refinement' ->
                    hsame provenance provenance' ->
                      hsame nameCert nameCert' ->
                        Cont level' cell' interval' ->
                          Cont interval' endpoint' radius' ->
                            PkgSig bundle provenance' pkg ->
                              DyadicMeshPacket level' cell' interval' endpoint' radius' order'
                                  transport' refinement' provenance' nameCert' bundle pkg ∧
                                hsame interval interval' := by
  intro packet sameLevel sameCell sameEndpoint sameRadius sameOrder sameTransport
    sameRefinement sameProvenance sameNameCert levelCellInterval' intervalEndpointRadius'
    provenancePkg'
  rcases packet with
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, radiusUnary, orderUnary,
      transportUnary, refinementUnary, provenanceUnary, nameCertUnary, levelCellInterval,
      intervalEndpointRadius, _provenancePkg⟩
  have sameInterval : hsame interval interval' :=
    cont_respects_hsame sameLevel sameCell levelCellInterval levelCellInterval'
  have levelUnary' : UnaryHistory level' := unary_transport levelUnary sameLevel
  have cellUnary' : UnaryHistory cell' := unary_transport cellUnary sameCell
  have intervalUnary' : UnaryHistory interval' :=
    unary_cont_closed levelUnary' cellUnary' levelCellInterval'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have orderUnary' : UnaryHistory order' := unary_transport orderUnary sameOrder
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have refinementUnary' : UnaryHistory refinement' :=
    unary_transport refinementUnary sameRefinement
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  exact
    ⟨⟨levelUnary', cellUnary', intervalUnary', endpointUnary', radiusUnary', orderUnary',
        transportUnary', refinementUnary', provenanceUnary', nameCertUnary',
        levelCellInterval', intervalEndpointRadius', provenancePkg'⟩,
      sameInterval⟩

theorem DyadicMeshPacket_rational_interval_coverage [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert coverage :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint coverage ->
        PkgSig bundle coverage pkg ->
          UnaryHistory interval ∧ UnaryHistory endpoint ∧ UnaryHistory coverage ∧
            Cont interval endpoint radius ∧ Cont interval endpoint coverage ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle coverage pkg := by
  intro packet intervalEndpointCoverage coveragePkg
  rcases packet with
    ⟨_levelUnary, _cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      _transportUnary, _refinementUnary, _provenanceUnary, _nameCertUnary,
      _levelCellInterval, intervalEndpointRadius, provenancePkg⟩
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointCoverage
  exact
    ⟨intervalUnary, endpointUnary, coverageUnary, intervalEndpointRadius,
      intervalEndpointCoverage, provenancePkg, coveragePkg⟩

theorem DyadicMeshPacket_standard_finite_mesh_bridge_boundary [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert meshCell
      realBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint meshCell ->
        Cont meshCell provenance realBoundary ->
          PkgSig bundle meshCell pkg ->
            PkgSig bundle realBoundary pkg ->
              UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧
                UnaryHistory meshCell ∧ UnaryHistory realBoundary ∧ Cont level cell interval ∧
                  Cont interval endpoint radius ∧ Cont interval endpoint meshCell ∧
                    Cont meshCell provenance realBoundary ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle meshCell pkg ∧ PkgSig bundle realBoundary pkg := by
  intro packet intervalEndpointMesh meshProvenanceBoundary meshPkg boundaryPkg
  rcases packet with
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      _transportUnary, _refinementUnary, provenanceUnary, _nameCertUnary, levelCellInterval,
      intervalEndpointRadius, provenancePkg⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointMesh
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceBoundary
  exact
    ⟨levelUnary, cellUnary, intervalUnary, meshUnary, boundaryUnary, levelCellInterval,
      intervalEndpointRadius, intervalEndpointMesh, meshProvenanceBoundary, provenancePkg,
      meshPkg, boundaryPkg⟩

end BEDC.Derived.DyadicMeshUp
