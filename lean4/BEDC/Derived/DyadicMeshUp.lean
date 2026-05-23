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

theorem DyadicMeshPacket_validatednumerics_handoff [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert containment
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint containment ->
        Cont containment provenance handoff ->
          PkgSig bundle containment pkg ->
            PkgSig bundle handoff pkg ->
              UnaryHistory level ∧ UnaryHistory cell ∧ UnaryHistory interval ∧
                UnaryHistory endpoint ∧ UnaryHistory containment ∧ UnaryHistory handoff ∧
                  Cont level cell interval ∧ Cont interval endpoint containment ∧
                    Cont containment provenance handoff ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle containment pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
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
    ⟨levelUnary, cellUnary, intervalUnary, endpointUnary, containmentUnary, handoffUnary,
      levelCellInterval, intervalEndpointContainment, containmentProvenanceHandoff,
      provenancePkg, containmentPkg, handoffPkg⟩

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

theorem DyadicMeshPacket_rationalinterval_coverage [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert coverage :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint coverage ->
        PkgSig bundle coverage pkg ->
          UnaryHistory interval ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
            UnaryHistory order ∧ UnaryHistory coverage ∧ Cont level cell interval ∧
              Cont interval endpoint radius ∧ Cont interval endpoint coverage ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle coverage pkg := by
  intro packet intervalEndpointCoverage coveragePkg
  rcases packet with
    ⟨_levelUnary, _cellUnary, intervalUnary, endpointUnary, radiusUnary, orderUnary,
      _transportUnary, _refinementUnary, _provenanceUnary, _nameCertUnary,
      levelCellInterval, intervalEndpointRadius, provenancePkg⟩
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointCoverage
  exact
    ⟨intervalUnary, endpointUnary, radiusUnary, orderUnary, coverageUnary,
      levelCellInterval, intervalEndpointRadius, intervalEndpointCoverage, provenancePkg,
      coveragePkg⟩

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

theorem DyadicMeshPacket_validated_terminal_readback_determinacy [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert meshCell
      realBoundary terminalRead validatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      Cont interval endpoint meshCell ->
        Cont meshCell provenance realBoundary ->
          Cont realBoundary transport terminalRead ->
            Cont terminalRead refinement validatedRead ->
              PkgSig bundle meshCell pkg ->
                PkgSig bundle realBoundary pkg ->
                  PkgSig bundle validatedRead pkg ->
                    UnaryHistory meshCell ∧
                      UnaryHistory realBoundary ∧
                        UnaryHistory terminalRead ∧
                          UnaryHistory validatedRead ∧
                            Cont interval endpoint meshCell ∧
                              Cont meshCell provenance realBoundary ∧
                                Cont realBoundary transport terminalRead ∧
                                  Cont terminalRead refinement validatedRead ∧
                                    PkgSig bundle validatedRead pkg ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row validatedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row realBoundary ∨
                                            hsame row terminalRead ∨ hsame row validatedRead)
                                        (fun row : BHist =>
                                          hsame row validatedRead ∧
                                            PkgSig bundle validatedRead pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory SemanticNameCert hsame
  intro packet intervalEndpointMesh meshProvenanceBoundary boundaryTransportTerminal
  intro terminalRefinementValidated _meshPkg _boundaryPkg validatedPkg
  rcases packet with
    ⟨_levelUnary, _cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      transportUnary, refinementUnary, provenanceUnary, _nameCertUnary, _levelCellInterval,
      _intervalEndpointRadius, _provenancePkg⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointMesh
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceBoundary
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed boundaryUnary transportUnary boundaryTransportTerminal
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed terminalUnary refinementUnary terminalRefinementValidated
  have sourceValidated :
      (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row) validatedRead := by
    exact ⟨hsame_refl validatedRead, validatedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row realBoundary ∨ hsame row terminalRead ∨ hsame row validatedRead)
        (fun row : BHist => hsame row validatedRead ∧ PkgSig bundle validatedRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro validatedRead sourceValidated
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, validatedPkg⟩
    }
  exact
    ⟨meshUnary, boundaryUnary, terminalUnary, validatedUnary, intervalEndpointMesh,
      meshProvenanceBoundary, boundaryTransportTerminal, terminalRefinementValidated,
      validatedPkg, cert⟩

theorem DyadicMeshPacket_common_refinement_endpoint_determinacy [AskSetup] [PackageSetup]
    {level cell interval endpoint radius order transport refinement provenance nameCert level'
      cell' interval' endpoint' radius' order' transport' refinement' provenance' nameCert'
      meshCell meshCell' realBoundary realBoundary' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicMeshPacket level cell interval endpoint radius order transport refinement provenance
        nameCert bundle pkg ->
      DyadicMeshPacket level' cell' interval' endpoint' radius' order' transport' refinement'
          provenance' nameCert' bundle pkg ->
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
                                Cont interval endpoint meshCell ->
                                  Cont meshCell provenance realBoundary ->
                                    Cont interval' endpoint' meshCell' ->
                                      Cont meshCell' provenance' realBoundary' ->
                                        PkgSig bundle meshCell pkg ->
                                          PkgSig bundle realBoundary pkg ->
                                            PkgSig bundle meshCell' pkg ->
                                              PkgSig bundle realBoundary' pkg ->
                                                hsame interval interval' ∧
                                                  UnaryHistory meshCell ∧
                                                    UnaryHistory meshCell' ∧
                                                      UnaryHistory realBoundary ∧
                                                        UnaryHistory realBoundary' ∧
                                                          Cont interval endpoint meshCell ∧
                                                            Cont interval' endpoint'
                                                              meshCell' ∧
                                                              PkgSig bundle meshCell pkg ∧
                                                                PkgSig bundle meshCell' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet _packet' sameLevel sameCell sameEndpoint sameRadius sameOrder
  intro sameTransport sameRefinement sameProvenance sameNameCert
  intro levelCellInterval' intervalEndpointRadius' provenancePkg'
  intro intervalEndpointMesh meshProvenanceBoundary intervalEndpointMesh'
  intro meshProvenanceBoundary' meshPkg _boundaryPkg meshPkg' _boundaryPkg'
  have stable :=
    DyadicMeshPacket_refinement_stability packet sameLevel sameCell sameEndpoint sameRadius
      sameOrder sameTransport sameRefinement sameProvenance sameNameCert levelCellInterval'
      intervalEndpointRadius' provenancePkg'
  rcases stable with ⟨targetPacket, sameInterval⟩
  rcases packet with
    ⟨_levelUnary, _cellUnary, intervalUnary, endpointUnary, _radiusUnary, _orderUnary,
      _transportUnary, _refinementUnary, provenanceUnary, _nameCertUnary, _levelCellInterval,
      _intervalEndpointRadius, _provenancePkg⟩
  rcases targetPacket with
    ⟨_levelUnary', _cellUnary', intervalUnary', endpointUnary', _radiusUnary', _orderUnary',
      _transportUnary', _refinementUnary', provenanceUnary', _nameCertUnary',
      _levelCellInterval'', _intervalEndpointRadius'', _provenancePkg''⟩
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed intervalUnary endpointUnary intervalEndpointMesh
  have meshUnary' : UnaryHistory meshCell' :=
    unary_cont_closed intervalUnary' endpointUnary' intervalEndpointMesh'
  have boundaryUnary : UnaryHistory realBoundary :=
    unary_cont_closed meshUnary provenanceUnary meshProvenanceBoundary
  have boundaryUnary' : UnaryHistory realBoundary' :=
    unary_cont_closed meshUnary' provenanceUnary' meshProvenanceBoundary'
  exact
    ⟨sameInterval, meshUnary, meshUnary', boundaryUnary, boundaryUnary',
      intervalEndpointMesh, intervalEndpointMesh', meshPkg, meshPkg'⟩

end BEDC.Derived.DyadicMeshUp
