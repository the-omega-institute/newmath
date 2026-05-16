import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyModulusWitnessLedgerCarrier [AskSetup] [PackageSetup]
    (source witness window normalizer tail dyadic readback sealRow transport route provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory witness ∧ UnaryHistory window ∧
    UnaryHistory normalizer ∧ UnaryHistory tail ∧ UnaryHistory dyadic ∧
      UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          hsame transport BHist.Empty ∧ Cont witness window normalizer ∧
            Cont normalizer tail dyadic ∧ Cont dyadic readback sealRow ∧
              Cont transport route provenance ∧ hsame route sealRow ∧
                PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem RegularCauchyModulusWitnessLedgerCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                  dyadic readback sealRow transport route provenance name bundle pkg ∧
                    hsame row endpoint)
              (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                  Cont dyadic readback sealRow ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sealTransportEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, sealUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have sealUnaryFromRoute : UnaryHistory sealRow :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackSeal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  have certCore :
      NameCert
        (fun row : BHist =>
          RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
              readback sealRow transport route provenance name bundle pkg ∧
            hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
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
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                dyadic readback sealRow transport route provenance name bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
              Cont dyadic readback sealRow ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport endpointUnary sourceRow.right.symm
        have endpointSameSeal : hsame endpoint sealRow :=
          by
            cases transportEmpty
            exact cont_deterministic sealTransportEndpoint (cont_right_unit sealRow)
        exact
          And.intro (hsame_trans sourceRow.right endpointSameSeal) rowUnary
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal, endpointPkg⟩
    }
  exact And.intro semantic endpointUnary

theorem RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        hsame endpoint sealRow ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier sealTransportEndpoint
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, sealUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, transportEmpty, _witnessWindowNormalizer,
    _normalizerTailDyadic, _dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have endpointSameSeal : hsame endpoint sealRow := by
    cases transportEmpty
    exact cont_deterministic sealTransportEndpoint (cont_right_unit sealRow)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  exact ⟨endpointSameSeal, endpointUnary⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_non_escape [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        PkgSig bundle endpoint pkg ->
          hsame endpoint sealRow ∧ UnaryHistory source ∧ UnaryHistory witness ∧
            UnaryHistory window ∧ UnaryHistory normalizer ∧ UnaryHistory tail ∧
              UnaryHistory dyadic ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
                  UnaryHistory name ∧ UnaryHistory endpoint ∧
                    Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                      Cont dyadic readback sealRow ∧ Cont transport route provenance ∧
                        hsame route sealRow ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointPkg
  have carrierPacket :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, witnessUnary, windowUnary, normalizerUnary, tailUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    _transportEmpty, witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
    transportRouteProvenance, routeSeal, provenancePkg, namePkg⟩ := carrier
  have det :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierPacket sealTransportEndpoint
  exact
    ⟨det.left, sourceUnary, witnessUnary, windowUnary, normalizerUnary, tailUnary,
      dyadicUnary, readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary,
      nameUnary, det.right, witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
      transportRouteProvenance, routeSeal, provenancePkg, namePkg, endpointPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_modulus_normalizer_tail_coherence [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory witness ∧ UnaryHistory window ∧ UnaryHistory normalizer ∧
            UnaryHistory tail ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
              UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                  Cont dyadic readback sealRow ∧ hsame endpoint sealRow ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointPkg
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, normalizerUnary, tailUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    transportEmpty, witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
    _transportRouteProvenance, _routeSeal, provenancePkg, _namePkg⟩ := carrier
  have endpointSameSeal : hsame endpoint sealRow := by
    cases transportEmpty
    exact cont_deterministic sealTransportEndpoint (cont_right_unit sealRow)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  exact
    ⟨witnessUnary, windowUnary, normalizerUnary, tailUnary, dyadicUnary, readbackUnary,
      sealUnary, endpointUnary, witnessWindowNormalizer, normalizerTailDyadic,
      dyadicReadbackSeal, endpointSameSeal, provenancePkg, endpointPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_completion_consumer_boundary [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route completionRead ->
          PkgSig bundle endpoint pkg ->
            PkgSig bundle completionRead pkg ->
              hsame endpoint sealRow ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                UnaryHistory readback ∧ UnaryHistory normalizer ∧ UnaryHistory tail ∧
                  UnaryHistory endpoint ∧ UnaryHistory completionRead ∧
                    Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                      Cont dyadic readback sealRow ∧ Cont endpoint route completionRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointRouteCompletion endpointPkg completionPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
          readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, _sealUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    provenancePkg, _namePkg⟩ := carrier
  have det :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed det.right routeUnary endpointRouteCompletion
  exact
    ⟨det.left, windowUnary, dyadicUnary, readbackUnary, normalizerUnary, tailUnary, det.right,
      completionUnary, witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
      endpointRouteCompletion, provenancePkg, endpointPkg, completionPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_window_budget_exhaustion [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        PkgSig bundle endpoint pkg ->
          hsame endpoint sealRow ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory readback ∧ UnaryHistory endpoint ∧ Cont witness window normalizer ∧
              Cont normalizer tail dyadic ∧ Cont dyadic readback sealRow ∧
                PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointPkg
  obtain ⟨_sourceUnary, _witnessUnary, windowUnary, _normalizerUnary, _tailUnary,
    dyadicUnary, readbackUnary, sealUnary, transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, transportEmpty, witnessWindowNormalizer, normalizerTailDyadic,
    dyadicReadbackSeal, _transportRouteProvenance, _routeSeal, _provenancePkg, _namePkg⟩ :=
    carrier
  have endpointSameSeal : hsame endpoint sealRow := by
    cases transportEmpty
    exact cont_deterministic sealTransportEndpoint (cont_right_unit sealRow)
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  exact
    ⟨endpointSameSeal, windowUnary, dyadicUnary, readbackUnary, endpointUnary,
      witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal, endpointPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_normalizer_tail_commutation [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name normalizer' dyadic' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont witness window normalizer' ->
        Cont normalizer' tail dyadic' ->
          hsame normalizer normalizer' ∧ hsame dyadic dyadic' ∧
            UnaryHistory normalizer' ∧ UnaryHistory dyadic' ∧
              Cont normalizer' tail dyadic' := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier witnessWindowNormalizer' normalizerTailDyadic'
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, _dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have normalizerSame : hsame normalizer normalizer' :=
    cont_respects_hsame (hsame_refl witness) (hsame_refl window) witnessWindowNormalizer
      witnessWindowNormalizer'
  have dyadicSame : hsame dyadic dyadic' :=
    cont_respects_hsame normalizerSame (hsame_refl tail) normalizerTailDyadic
      normalizerTailDyadic'
  have normalizerUnary' : UnaryHistory normalizer' :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer'
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_cont_closed normalizerUnary' tailUnary normalizerTailDyadic'
  exact
    ⟨normalizerSame, dyadicSame, normalizerUnary', dyadicUnary', normalizerTailDyadic'⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_completion_seal_handoff_totality
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route completionRead ->
          PkgSig bundle endpoint pkg ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                      dyadic readback sealRow transport route provenance name bundle pkg ∧
                    hsame row completionRead)
                (fun row : BHist =>
                  Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                    Cont dyadic readback sealRow ∧ Cont sealRow transport endpoint ∧
                      Cont endpoint route row ∧ PkgSig bundle completionRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle completionRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sealTransportEndpoint endpointRouteCompletion _endpointPkg completionPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, _sealUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    provenancePkg, namePkg⟩ := carrier
  have det :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have _sealUnaryFromRoute : UnaryHistory sealRow :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed det.right routeUnary endpointRouteCompletion
  exact {
    core := {
      carrier_inhabited := Exists.intro completionRead
        (And.intro carrierWitness (hsame_refl completionRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
          sealTransportEndpoint,
          cont_result_hsame_transport endpointRouteCompletion (hsame_symm source.right),
          completionPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport completionUnary (hsame_symm source.right), provenancePkg, namePkg,
          completionPkg⟩
  }

theorem RegularCauchyModulusWitnessLedgerCarrier_route_field_faithfulness [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont sealRow transport endpoint' ->
          PkgSig bundle endpoint pkg ->
            PkgSig bundle endpoint' pkg ->
              hsame endpoint endpoint' /\ UnaryHistory endpoint /\ UnaryHistory endpoint' /\
                Cont witness window normalizer /\ Cont normalizer tail dyadic /\
                  Cont dyadic readback sealRow /\ PkgSig bundle endpoint pkg /\
                    PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sealTransportEndpoint sealTransportEndpoint' endpointPkg endpointPkg'
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
          readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have detEndpoint :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have detEndpoint' :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint') carrierWitness
      sealTransportEndpoint'
  have endpointSame : hsame endpoint endpoint' :=
    hsame_trans detEndpoint.left (hsame_symm detEndpoint'.left)
  exact
    ⟨endpointSame, detEndpoint.right, detEndpoint'.right, witnessWindowNormalizer,
      normalizerTailDyadic, dyadicReadbackSeal, endpointPkg, endpointPkg'⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_real_seal_consumer_exactness
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle consumer pkg ->
            hsame (append dyadic (append readback transport)) endpoint ∧
              hsame (append endpoint route) consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sealTransportEndpoint endpointRouteConsumer consumerPkg
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, transportEmpty, _witnessWindowNormalizer,
    _normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  constructor
  · cases transportEmpty
    cases dyadicReadbackSeal
    cases sealTransportEndpoint
    rfl
  · exact ⟨endpointRouteConsumer.symm, consumerPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_seal_source_pullback [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle consumer pkg ->
            hsame endpoint sealRow ∧ hsame (append endpoint route) consumer ∧
              hsame route sealRow ∧ Cont witness window normalizer ∧
                Cont normalizer tail dyadic ∧ Cont dyadic readback sealRow ∧
                  Cont endpoint route consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointRouteConsumer consumerPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have sealDeterminacy :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have consumerExactness :=
    RegularCauchyModulusWitnessLedgerCarrier_real_seal_consumer_exactness
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) (consumer := consumer)
      carrierWitness sealTransportEndpoint endpointRouteConsumer consumerPkg
  exact
    ⟨sealDeterminacy.left, consumerExactness.right.left, routeSeal,
      witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
      endpointRouteConsumer, consumerPkg⟩

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
