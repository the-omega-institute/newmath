import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ValidatedNumericsPacket [AskSetup] [PackageSetup]
    (interval precision modulus observation readback transport containment provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
    UnaryHistory observation ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
      UnaryHistory containment ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont precision modulus observation ∧ Cont observation readback transport ∧
          Cont observation interval containment ∧ Cont containment provenance name ∧
            PkgSig bundle name pkg

theorem ValidatedNumericsPacket_carrier_classifier_obligations [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
        UnaryHistory observation ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
          UnaryHistory containment ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
            Cont precision modulus observation ∧ Cont observation readback transport ∧
              Cont observation interval containment ∧ Cont containment provenance name ∧
                PkgSig bundle name pkg := by
  intro packet
  exact packet

theorem ValidatedNumericsPacket_precision_refinement_containment
    [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      refinedPrecision refinedObservation refinedContainment refinedName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      hsame precision refinedPrecision ->
        hsame observation refinedObservation ->
          hsame containment refinedContainment ->
            hsame name refinedName ->
              Cont refinedPrecision modulus refinedObservation ->
                Cont refinedObservation interval refinedContainment ->
                  PkgSig bundle refinedName pkg ->
                    ValidatedNumericsPacket interval refinedPrecision modulus refinedObservation
                        readback transport refinedContainment provenance refinedName bundle pkg ∧
                      hsame observation refinedObservation ∧
                        hsame containment refinedContainment := by
  intro packet samePrecision sameObservation sameContainment sameName refinedPrecisionModulus
    refinedObservationInterval refinedPkg
  obtain ⟨intervalUnary, precisionUnary, modulusUnary, observationUnary, readbackUnary,
    transportUnary, containmentUnary, provenanceUnary, nameUnary, _precisionModulusObservation,
    observationReadbackTransport, _observationIntervalContainment,
    containmentProvenanceName, _namePkg⟩ := packet
  have refinedPrecisionUnary : UnaryHistory refinedPrecision :=
    unary_transport precisionUnary samePrecision
  have refinedObservationUnary : UnaryHistory refinedObservation :=
    unary_transport observationUnary sameObservation
  have refinedContainmentUnary : UnaryHistory refinedContainment :=
    unary_transport containmentUnary sameContainment
  have refinedNameUnary : UnaryHistory refinedName :=
    unary_transport nameUnary sameName
  have refinedObservationReadbackTransport : Cont refinedObservation readback transport := by
    cases sameObservation
    exact observationReadbackTransport
  have refinedContainmentProvenanceName : Cont refinedContainment provenance refinedName := by
    cases sameContainment
    cases sameName
    exact containmentProvenanceName
  exact
    ⟨⟨intervalUnary, refinedPrecisionUnary, modulusUnary, refinedObservationUnary,
        readbackUnary, transportUnary, refinedContainmentUnary, provenanceUnary,
        refinedNameUnary, refinedPrecisionModulus, refinedObservationReadbackTransport,
        refinedObservationInterval, refinedContainmentProvenanceName, refinedPkg⟩,
      sameObservation, sameContainment⟩

theorem ValidatedNumericsPacket_containment_ledger_transport [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      observation' containment' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      hsame observation observation' ->
        hsame containment containment' ->
          Cont observation' interval containment' ->
            UnaryHistory interval ∧ UnaryHistory observation' ∧ UnaryHistory containment' ∧
              Cont observation' interval containment' ∧ Cont precision modulus observation ∧
                PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro packet sameObservation sameContainment observationIntervalContainment'
  obtain ⟨intervalUnary, _precisionUnary, _modulusUnary, observationUnary, _readbackUnary,
    _transportUnary, containmentUnary, _provenanceUnary, _nameUnary,
    precisionModulusObservation, _observationReadbackTransport,
    _observationIntervalContainment, _containmentProvenanceName, namePkg⟩ := packet
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary sameObservation
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  exact
    ⟨intervalUnary, observationUnary', containmentUnary', observationIntervalContainment',
      precisionModulusObservation, namePkg⟩

theorem ValidatedNumericsReadbackPacket_real_readback_soundness [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance name finiteRead
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory observation ->
            UnaryHistory readback ->
              UnaryHistory containment ->
                UnaryHistory provenance ->
                  UnaryHistory name ->
                    Cont modulus precision observation ->
                      Cont observation readback finiteRead ->
                        Cont interval containment sealRow ->
                          PkgSig bundle name pkg ->
                            PkgSig bundle sealRow pkg ->
                              UnaryHistory finiteRead ∧
                                UnaryHistory sealRow ∧
                                  Cont modulus precision observation ∧
                                    Cont observation readback finiteRead ∧
                                      Cont interval containment sealRow ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle sealRow pkg := by
  intro intervalUnary _precisionUnary _modulusUnary observationUnary readbackUnary containmentUnary
  intro _provenanceUnary _nameUnary modulusPrecision observationReadback intervalContainment
  intro namePkg sealPkg
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed observationUnary readbackUnary observationReadback
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  exact ⟨finiteReadUnary, sealRowUnary, modulusPrecision, observationReadback, intervalContainment,
    namePkg, sealPkg⟩

theorem ValidatedNumericsReadbackPacket_precision_refinement_containment [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance name refinedPrecision
      refinedObservation refinedContainment refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory observation ->
            UnaryHistory readback ->
              UnaryHistory containment ->
                UnaryHistory provenance ->
                  UnaryHistory name ->
                    hsame precision refinedPrecision ->
                      hsame observation refinedObservation ->
                        Cont modulus refinedPrecision refinedObservation ->
                          Cont refinedObservation readback refinedRead ->
                            Cont interval containment refinedContainment ->
                              PkgSig bundle refinedContainment pkg ->
                                UnaryHistory refinedPrecision ∧ UnaryHistory refinedObservation ∧
                                  UnaryHistory refinedRead ∧ UnaryHistory refinedContainment ∧
                                    Cont modulus refinedPrecision refinedObservation ∧
                                      Cont refinedObservation readback refinedRead ∧
                                        Cont interval containment refinedContainment ∧
                                          PkgSig bundle refinedContainment pkg := by
  intro intervalUnary precisionUnary _modulusUnary observationUnary readbackUnary containmentUnary
  intro _provenanceUnary _nameUnary samePrecision sameObservation modulusPrecisionObservation
  intro observationReadback intervalContainment containmentPkg
  have refinedPrecisionUnary : UnaryHistory refinedPrecision :=
    unary_transport precisionUnary samePrecision
  have refinedObservationUnary : UnaryHistory refinedObservation :=
    unary_transport observationUnary sameObservation
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed refinedObservationUnary readbackUnary observationReadback
  have refinedContainmentUnary : UnaryHistory refinedContainment :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  exact
    ⟨refinedPrecisionUnary, refinedObservationUnary, refinedReadUnary, refinedContainmentUnary,
      modulusPrecisionObservation, observationReadback, intervalContainment, containmentPkg⟩

theorem ValidatedNumericsPacket_refined_readback_containment_determinacy [AskSetup]
    [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      refinedPrecision refinedObservation refinedContainment refinedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      hsame precision refinedPrecision ->
        hsame observation refinedObservation ->
          Cont refinedPrecision modulus refinedObservation ->
            Cont refinedObservation readback refinedRead ->
              Cont interval containment refinedContainment ->
                Cont interval containment sealRead ->
                  PkgSig bundle refinedContainment pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory refinedRead ∧ UnaryHistory refinedContainment ∧
                        UnaryHistory sealRead ∧ Cont refinedObservation readback refinedRead ∧
                          Cont interval containment refinedContainment ∧
                            Cont interval containment sealRead ∧
                              PkgSig bundle refinedContainment pkg ∧
                                PkgSig bundle sealRead pkg := by
  intro packet samePrecision sameObservation _refinedPrecisionModulus refinedObservationReadback
  intro intervalContainment intervalSealRead containmentPkg sealPkg
  obtain ⟨intervalUnary, precisionUnary, _modulusUnary, observationUnary, readbackUnary,
    _transportUnary, containmentUnary, _provenanceUnary, _nameUnary,
    _precisionModulusObservation, _observationReadbackTransport,
    _observationIntervalContainment, _containmentProvenanceName, _namePkg⟩ := packet
  have refinedPrecisionUnary : UnaryHistory refinedPrecision :=
    unary_transport precisionUnary samePrecision
  have refinedObservationUnary : UnaryHistory refinedObservation :=
    unary_transport observationUnary sameObservation
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed refinedObservationUnary readbackUnary refinedObservationReadback
  have refinedContainmentUnary : UnaryHistory refinedContainment :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary containmentUnary intervalSealRead
  exact
    ⟨refinedReadUnary, refinedContainmentUnary, sealReadUnary, refinedObservationReadback,
      intervalContainment, intervalSealRead, containmentPkg, sealPkg⟩

theorem ValidatedNumericsFiniteEnclosure_exported_bridge [AskSetup] [PackageSetup]
    {interval endpoint precision modulus observation readback containment transport provenance name
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory endpoint ->
        UnaryHistory precision ->
          UnaryHistory modulus ->
            UnaryHistory observation ->
              UnaryHistory readback ->
                UnaryHistory containment ->
                  UnaryHistory transport ->
                    UnaryHistory provenance ->
                      UnaryHistory name ->
                        Cont precision modulus observation ->
                          Cont observation readback containment ->
                            Cont containment provenance bridge ->
                              PkgSig bundle name pkg ->
                                PkgSig bundle bridge pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row bridge ∧ UnaryHistory row ∧
                                        PkgSig bundle row pkg)
                                    (fun row : BHist =>
                                      UnaryHistory interval ∧ UnaryHistory endpoint ∧
                                        UnaryHistory precision ∧
                                          Cont containment provenance row)
                                    (fun row : BHist =>
                                      PkgSig bundle row pkg ∧
                                        Cont observation readback containment)
                                    (fun row row' : BHist =>
                                      PkgSig bundle row pkg ∧ hsame row row') := by
  intro intervalUnary endpointUnary precisionUnary _modulusUnary _observationUnary
  intro _readbackUnary containmentUnary _transportUnary provenanceUnary _nameUnary
  intro _precisionModulusObservation observationReadbackContainment containmentProvenanceBridge
  intro _namePkg bridgePkg
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed containmentUnary provenanceUnary containmentProvenanceBridge
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridge ⟨hsame_refl bridge, bridgeUnary, bridgePkg⟩
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
      exact
        ⟨intervalUnary, endpointUnary, precisionUnary, containmentProvenanceBridge⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, observationReadbackContainment⟩
  }

theorem ValidatedNumericsKernel_dependency_boundary [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory readback ->
            Cont modulus precision observation ->
              Cont observation readback containment ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle localName pkg ->
                    UnaryHistory observation ∧ UnaryHistory containment ∧
                      Cont modulus precision observation ∧
                        Cont observation readback containment ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  intro _intervalUnary precisionUnary modulusUnary readbackUnary modulusPrecision
    observationReadback provenancePkg localNamePkg
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed modulusUnary precisionUnary modulusPrecision
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed observationUnary readbackUnary observationReadback
  exact
    ⟨observationUnary, containmentUnary, modulusPrecision, observationReadback, provenancePkg,
      localNamePkg⟩

theorem ValidatedNumericsUp_StdBridge [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      Cont containment provenance bridge ->
        PkgSig bundle bridge pkg ->
          UnaryHistory bridge ∧ Cont containment provenance bridge ∧
            PkgSig bundle bridge pkg ∧
              SemanticNameCert
                (fun row : BHist =>
                  hsame row bridge ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  UnaryHistory interval ∧ UnaryHistory precision ∧
                    Cont containment provenance row)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ Cont containment provenance row)
                (fun row row' : BHist =>
                  PkgSig bundle row pkg ∧ hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro packet containmentProvenanceBridge bridgePkg
  obtain ⟨intervalUnary, precisionUnary, _modulusUnary, _observationUnary, _readbackUnary,
    _transportUnary, containmentUnary, provenanceUnary, _nameUnary, _precisionModulusObservation,
    _observationReadbackTransport, _observationIntervalContainment, _containmentProvenanceName,
    _namePkg⟩ := packet
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed containmentUnary provenanceUnary containmentProvenanceBridge
  have bridgeCert :
      SemanticNameCert
        (fun row : BHist => hsame row bridge ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          UnaryHistory interval ∧ UnaryHistory precision ∧ Cont containment provenance row)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont containment provenance row)
        (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited :=
        Exists.intro bridge ⟨hsame_refl bridge, bridgeUnary, bridgePkg⟩
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
      exact ⟨intervalUnary, precisionUnary, containmentProvenanceBridge⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨sourceRow.right.right, containmentProvenanceBridge⟩
  }
  exact ⟨bridgeUnary, containmentProvenanceBridge, bridgePkg, bridgeCert⟩

theorem ValidatedNumericsPacket_interval_enclosure_obligation [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      enclosureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      Cont interval containment enclosureRead ->
        PkgSig bundle enclosureRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row enclosureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun _row : BHist =>
                UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
                  Cont observation interval containment)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ Cont interval containment enclosureRead)
              (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') ∧
            UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
              UnaryHistory observation ∧ UnaryHistory containment ∧ UnaryHistory enclosureRead ∧
                Cont precision modulus observation ∧ Cont observation interval containment ∧
                  Cont interval containment enclosureRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle enclosureRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro packet enclosureRoute enclosurePkg
  obtain ⟨intervalUnary, precisionUnary, modulusUnary, observationUnary, _readbackUnary,
    _transportUnary, containmentUnary, _provenanceUnary, _nameUnary,
    precisionModulusObservation, _observationReadbackTransport,
    observationIntervalContainment, _containmentProvenanceName, namePkg⟩ := packet
  have enclosureUnary : UnaryHistory enclosureRead :=
    unary_cont_closed intervalUnary containmentUnary enclosureRoute
  have sourceAtEnclosure :
      hsame enclosureRead enclosureRead ∧ UnaryHistory enclosureRead ∧
        PkgSig bundle enclosureRead pkg :=
    ⟨hsame_refl enclosureRead, enclosureUnary, enclosurePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row enclosureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
              Cont observation interval containment)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont interval containment enclosureRead)
          (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := {
    core := {
      carrier_inhabited := Exists.intro enclosureRead sourceAtEnclosure
      equiv_refl := by
        intro row source
        exact ⟨source.right.right, hsame_refl row⟩
      equiv_symm := by
        intro row other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left,
            hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact
        ⟨intervalUnary, precisionUnary, modulusUnary, observationIntervalContainment⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨source.right.right, enclosureRoute⟩
  }
  exact
    ⟨cert, intervalUnary, precisionUnary, modulusUnary, observationUnary, containmentUnary,
      enclosureUnary, precisionModulusObservation, observationIntervalContainment,
      enclosureRoute, namePkg, enclosurePkg⟩

theorem ValidatedNumericsPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      enclosureRead bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      Cont interval containment enclosureRead ->
        Cont containment provenance bridge ->
          PkgSig bundle enclosureRead pkg ->
            PkgSig bundle bridge pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row bridge ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
                    Cont observation interval containment ∧ Cont containment provenance row)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ Cont containment provenance bridge)
                (fun row row' : BHist => PkgSig bundle row pkg ∧ hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro packet enclosureRoute containmentProvenanceBridge _enclosurePkg bridgePkg
  obtain ⟨intervalUnary, precisionUnary, modulusUnary, _observationUnary, _readbackUnary,
    _transportUnary, containmentUnary, provenanceUnary, _nameUnary, _precisionModulusObservation,
    _observationReadbackTransport, observationIntervalContainment, _containmentProvenanceName,
    _namePkg⟩ := packet
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed containmentUnary provenanceUnary containmentProvenanceBridge
  have sourceAtBridge :
      hsame bridge bridge ∧ UnaryHistory bridge ∧ PkgSig bundle bridge pkg :=
    ⟨hsame_refl bridge, bridgeUnary, bridgePkg⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro bridge sourceAtBridge
      equiv_refl := by
        intro row source
        exact ⟨source.right.right, hsame_refl row⟩
      equiv_symm := by
        intro row _other classified
        cases classified.right
        exact ⟨classified.left, hsame_refl row⟩
      equiv_trans := by
        intro _row _middle _other leftClassified rightClassified
        exact
          ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _other classified source
        cases classified.right
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact
        ⟨intervalUnary, precisionUnary, modulusUnary, observationIntervalContainment,
          containmentProvenanceBridge⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨source.right.right, containmentProvenanceBridge⟩
  }

theorem ValidatedNumericsPacket_public_finite_enclosure_consumer_certificate [AskSetup]
    [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      refinedPrecision refinedObservation refinedContainment refinedRead enclosureRead bridge :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      hsame precision refinedPrecision ->
        hsame observation refinedObservation ->
          Cont refinedPrecision modulus refinedObservation ->
            Cont refinedObservation readback refinedRead ->
              Cont interval containment refinedContainment ->
                Cont interval containment enclosureRead ->
                  Cont containment provenance bridge ->
                    PkgSig bundle refinedContainment pkg ->
                      PkgSig bundle enclosureRead pkg ->
                        PkgSig bundle bridge pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row enclosureRead ∧ UnaryHistory row ∧
                                  PkgSig bundle row pkg)
                              (fun _row : BHist =>
                                UnaryHistory interval ∧ UnaryHistory precision ∧
                                  UnaryHistory modulus ∧ Cont observation interval containment)
                              (fun row : BHist =>
                                PkgSig bundle row pkg ∧
                                  Cont interval containment enclosureRead)
                              (fun row row' : BHist =>
                                PkgSig bundle row pkg ∧ hsame row row') ∧
                            UnaryHistory refinedRead ∧ UnaryHistory refinedContainment ∧
                              UnaryHistory enclosureRead ∧
                                Cont refinedObservation readback refinedRead ∧
                                  Cont interval containment refinedContainment ∧
                                    Cont interval containment enclosureRead ∧
                                      PkgSig bundle refinedContainment pkg ∧
                                        PkgSig bundle enclosureRead pkg ∧
                                          SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row bridge ∧ UnaryHistory row ∧
                                                PkgSig bundle row pkg)
                                            (fun row : BHist =>
                                              UnaryHistory interval ∧
                                                UnaryHistory precision ∧
                                                  UnaryHistory modulus ∧
                                                    Cont observation interval containment ∧
                                                      Cont containment provenance row)
                                            (fun row : BHist =>
                                              PkgSig bundle row pkg ∧
                                                Cont containment provenance bridge)
                                            (fun row row' : BHist =>
                                              PkgSig bundle row pkg ∧ hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro packet samePrecision sameObservation refinedPrecisionModulus refinedObservationReadback
  intro refinedContainmentRoute enclosureRoute containmentProvenanceBridge refinedPkg
  intro enclosurePkg bridgePkg
  have enclosureSurface :=
    ValidatedNumericsPacket_interval_enclosure_obligation
      packet enclosureRoute enclosurePkg
  have refinedSurface :=
    ValidatedNumericsPacket_refined_readback_containment_determinacy
      packet samePrecision sameObservation refinedPrecisionModulus refinedObservationReadback
      refinedContainmentRoute enclosureRoute refinedPkg enclosurePkg
  have bridgeSurface :=
    ValidatedNumericsPacket_namecert_obligation_surface
      packet enclosureRoute containmentProvenanceBridge enclosurePkg bridgePkg
  exact
    ⟨enclosureSurface.left, refinedSurface.left, refinedSurface.right.left,
      refinedSurface.right.right.left, refinedSurface.right.right.right.left,
      refinedSurface.right.right.right.right.left,
      refinedSurface.right.right.right.right.right.left,
      refinedSurface.right.right.right.right.right.right.left,
      refinedSurface.right.right.right.right.right.right.right, bridgeSurface⟩

theorem ValidatedNumericsPacket_five_row_namecert_sketch [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg →
      UnaryHistory interval ∧ UnaryHistory precision ∧ UnaryHistory modulus ∧
        UnaryHistory observation ∧ UnaryHistory readback ∧
          Cont precision modulus observation ∧ Cont observation readback transport ∧
            Cont observation interval containment ∧ Cont containment provenance name ∧
              PkgSig bundle name pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row name ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row interval ∨ hsame row modulus ∨ hsame row observation ∨
                      hsame row readback ∨ hsame row name)
                  (fun row : BHist => hsame row name ∧ PkgSig bundle name pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro packet
  obtain ⟨intervalUnary, precisionUnary, modulusUnary, observationUnary, readbackUnary,
    _transportUnary, _containmentUnary, _provenanceUnary, nameUnary,
    precisionModulusObservation, observationReadbackTransport, observationIntervalContainment,
    containmentProvenanceName, namePkg⟩ := packet
  have sourceAtName : hsame name name ∧ UnaryHistory name :=
    ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row interval ∨ hsame row modulus ∨ hsame row observation ∨
            hsame row readback ∨ hsame row name)
        (fun row : BHist => hsame row name ∧ PkgSig bundle name pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro name sourceAtName
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
        intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact
    ⟨intervalUnary, precisionUnary, modulusUnary, observationUnary, readbackUnary,
      precisionModulusObservation, observationReadbackTransport, observationIntervalContainment,
      containmentProvenanceName, namePkg, cert⟩

end BEDC.Derived.ValidatedNumericsUp
