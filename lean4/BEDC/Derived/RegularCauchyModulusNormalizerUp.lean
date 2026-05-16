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

end BEDC.Derived.RegularCauchyModulusNormalizerUp
