import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyModulusNormalizerCarrier [AskSetup] [PackageSetup]
    (x y muX muY meet window dyadic readback sealRow transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
    UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
      UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont muX muY meet ∧ Cont meet window dyadic ∧ Cont dyadic readback sealRow ∧
            Cont sealRow transport route ∧ Cont route provenance name ∧
              PkgSig bundle meet pkg ∧ PkgSig bundle name pkg

theorem RegularCauchyModulusNormalizerCarrier_source_exposure_obligation [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      PkgSig bundle meet pkg ->
        SemanticNameCert
            (fun row : BHist =>
              RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                  sealRow transport route provenance name bundle pkg ∧
                hsame row meet)
            (fun row : BHist => hsame row meet ∧ UnaryHistory row)
            (fun _row : BHist =>
              UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
                Cont muX muY meet ∧ PkgSig bundle meet pkg)
            hsame ∧
          UnaryHistory meet := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier meetPkg
  have carrierWitness := carrier
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, _windowUnary, _dyadicUnary,
    _readbackUnary, _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              hsame row meet)
          (fun row : BHist => hsame row meet ∧ UnaryHistory row)
          (fun _row : BHist =>
            UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
              Cont muX muY meet ∧ PkgSig bundle meet pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro meet (And.intro carrierWitness (hsame_refl meet))
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
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, unary_transport meetUnary sourceRow.right.symm⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨xUnary, yUnary, muXUnary, muYUnary, sourceMeet, meetPkg⟩
    }
  exact ⟨cert, meetUnary⟩

theorem RegularCauchyModulusNormalizerCarrier_shared_window_obligation [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont dyadic readback endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                    readback sealRow transport route provenance name bundle pkg ∧
                  hsame row dyadic)
              (fun row : BHist => hsame row dyadic ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont muX muY meet ∧ Cont meet window dyadic ∧
                  Cont dyadic readback endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
              UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier dyadicReadbackEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, windowUnary,
    dyadicUnary, readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, sourceMeet, meetWindowDyadic, _dyadicReadbackSeal,
    _sealTransportRoute, _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackEndpoint
  have sourceAtDyadic :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame dyadic dyadic :=
    And.intro carrierWitness (hsame_refl dyadic)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                readback sealRow transport route provenance name bundle pkg ∧
              hsame row dyadic)
          (fun row : BHist => hsame row dyadic ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧
              Cont dyadic readback endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadic sourceAtDyadic
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.right, unary_transport dyadicUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact ⟨sourceMeet, meetWindowDyadic, dyadicReadbackEndpoint, endpointPkg⟩
  }
  exact ⟨cert, windowUnary, dyadicUnary, readbackUnary, endpointUnary⟩

theorem RegularCauchyModulusNormalizerCarrier_seal_replay_obligation [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont route provenance endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                    readback sealRow transport route provenance name bundle pkg ∧
                  hsame row sealRow)
              (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                  Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary,
    _dyadicUnary, _readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary,
    _nameUnary, _sourceMeet, _meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceEndpoint
  have sourceAtSeal :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame sealRow sealRow :=
    And.intro carrierWitness (hsame_refl sealRow)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                readback sealRow transport route provenance name bundle pkg ∧
              hsame row sealRow)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
              Cont route provenance endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact ⟨source.right, unary_transport sealUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact ⟨dyadicReadbackSeal, sealTransportRoute, routeProvenanceEndpoint, endpointPkg⟩
  }
  exact ⟨cert, sealUnary, transportUnary, routeUnary, provenanceUnary, endpointUnary⟩

theorem RegularCauchyModulusNormalizerCarrier_common_window [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont meet window dyadic ->
        Cont window dyadic comparisonRead ->
          PkgSig bundle comparisonRead pkg ->
            UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory comparisonRead ∧ Cont muX muY meet ∧
                Cont meet window dyadic ∧ Cont window dyadic comparisonRead ∧
                  PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier meetWindowDyadic windowDyadicComparisonRead comparisonPkg
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, windowUnary,
    dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, sourceMeet, _carrierMeetWindowDyadic,
    _dyadicReadbackSeal, _sealTransportRoute, _routeProvenanceName, _meetPkg,
    _namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicComparisonRead
  exact
    ⟨meetUnary, windowUnary, dyadicUnary, comparisonUnary, sourceMeet, meetWindowDyadic,
      windowDyadicComparisonRead, comparisonPkg⟩

theorem RegularCauchyModulusNormalizerCarrier_non_escape [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont route provenance endpoint ->
        PkgSig bundle endpoint pkg ->
          UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
            UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                  UnaryHistory endpoint ∧ Cont muX muY meet ∧ Cont meet window dyadic ∧
                    Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                      Cont route provenance endpoint ∧ PkgSig bundle meet pkg ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier routeProvenanceEndpoint endpointPkg
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
    _routeProvenanceName, meetPkg, namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceEndpoint
  exact
    ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      endpointUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
      routeProvenanceEndpoint, meetPkg, namePkg, endpointPkg⟩

theorem RegularCauchyModulusNormalizerCarrier_nonescape [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name audit :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont route provenance audit →
        PkgSig bundle name pkg →
          PkgSig bundle audit pkg →
            SemanticNameCert
                (fun row : BHist =>
                  RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                      readback sealRow transport route provenance name bundle pkg ∧
                    hsame row name)
                (fun row : BHist => hsame row name ∧ UnaryHistory row)
                (fun _row : BHist =>
                  PkgSig bundle name pkg ∧ PkgSig bundle audit pkg ∧
                    Cont route provenance audit)
                hsame ∧
              UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
                UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                  UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
                    UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                      UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceAudit namePkg auditPkg
  have carrierWitness := carrier
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    _sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _carrierNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceAudit
  have sourceAtName :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame name name :=
    And.intro carrierWitness (hsame_refl name)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              hsame row name)
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle audit pkg ∧
              Cont route provenance audit)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name sourceAtName
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport nameUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact ⟨namePkg, auditPkg, routeProvenanceAudit⟩
  }
  exact
    ⟨cert, xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
      auditUnary⟩

theorem RegularCauchyModulusNormalizerCarrier_source_meet_window_seal_triad [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      comparisonRead sealReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont window dyadic comparisonRead →
        Cont route provenance sealReplay →
          PkgSig bundle comparisonRead pkg →
            PkgSig bundle sealReplay pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                        readback sealRow transport route provenance name bundle pkg ∧
                      hsame row route)
                  (fun row : BHist => hsame row route ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    Cont muX muY meet ∧ Cont meet window dyadic ∧
                      Cont window dyadic comparisonRead ∧ Cont sealRow transport route ∧
                        Cont route provenance sealReplay ∧ PkgSig bundle comparisonRead pkg ∧
                          PkgSig bundle sealReplay pkg)
                  hsame ∧
                UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory sealRow ∧
                    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
                      UnaryHistory sealReplay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier windowDyadicComparison routeProvenanceSeal comparisonPkg sealPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, windowUnary, dyadicUnary,
    _readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, _nameUnary,
    sourceMeet, meetWindowDyadic, _dyadicReadbackSeal, sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicComparison
  have sealReplayUnary : UnaryHistory sealReplay :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceSeal
  have sourceAtRoute :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame route route :=
    And.intro carrierWitness (hsame_refl route)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                readback sealRow transport route provenance name bundle pkg ∧
              hsame row route)
          (fun row : BHist => hsame row route ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧
              Cont window dyadic comparisonRead ∧ Cont sealRow transport route ∧
                Cont route provenance sealReplay ∧ PkgSig bundle comparisonRead pkg ∧
                  PkgSig bundle sealReplay pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro route sourceAtRoute
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport routeUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨sourceMeet, meetWindowDyadic, windowDyadicComparison, sealTransportRoute,
          routeProvenanceSeal, comparisonPkg, sealPkg⟩
  }
  exact
    ⟨cert, meetUnary, windowUnary, dyadicUnary, comparisonUnary, sealUnary, transportUnary,
      routeUnary, provenanceUnary, sealReplayUnary⟩

theorem RegularCauchyModulusNormalizerCarrier_tail_budget_extraction [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont route provenance tailRead →
        PkgSig bundle tailRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                  sealRow transport route provenance name bundle pkg ∧
                hsame row tailRead)
            (fun row : BHist =>
              Cont muX muY meet ∧ Cont meet window dyadic ∧
                Cont dyadic readback sealRow ∧ Cont route provenance row)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle tailRead pkg ∧ PkgSig bundle name pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeProvenanceTail tailPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, routeUnary, provenanceUnary,
    _nameUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceTail
  have sourceAtTail :
      RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
          sealRow transport route provenance name bundle pkg ∧
        hsame tailRead tailRead :=
    And.intro carrierWitness (hsame_refl tailRead)
  exact {
    core := {
      carrier_inhabited := Exists.intro tailRead sourceAtTail
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      have routeTailRow : Cont route provenance row :=
        cont_result_hsame_transport routeProvenanceTail (hsame_symm source.right)
      exact ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, routeTailRow⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport tailUnary (hsame_symm source.right), tailPkg, namePkg⟩
  }

theorem RegularCauchyModulusNormalizerCarrier_source_exchange_stability [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      Cont window dyadic comparisonRead ->
        PkgSig bundle comparisonRead pkg ->
          UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
            UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory comparisonRead ∧ Cont muX muY meet ∧
                Cont meet window dyadic ∧ Cont window dyadic comparisonRead ∧
                  PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier windowDyadicComparisonRead comparisonPkg
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
    _readbackUnary, _sealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameUnary, sourceMeet, meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicComparisonRead
  exact
    ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, windowUnary, dyadicUnary,
      comparisonUnary, sourceMeet, meetWindowDyadic, windowDyadicComparisonRead,
      comparisonPkg⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
