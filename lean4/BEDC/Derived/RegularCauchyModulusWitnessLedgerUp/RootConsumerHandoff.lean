import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusWitnessLedgerCarrier_root_consumer_handoff_totality
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle endpoint pkg ->
            PkgSig bundle consumer pkg ->
              hsame endpoint sealRow ∧ UnaryHistory source ∧ UnaryHistory witness ∧
                UnaryHistory window ∧ UnaryHistory normalizer ∧ UnaryHistory tail ∧
                  UnaryHistory dyadic ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                    UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
                      UnaryHistory name ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
                        Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                          Cont dyadic readback sealRow ∧ Cont endpoint route consumer ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle endpoint pkg ∧
                                PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointRouteConsumer endpointPkg consumerPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨sourceUnary, witnessUnary, windowUnary, normalizerUnary, tailUnary, dyadicUnary,
    readbackUnary, sealUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    _transportEmpty, witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
    _transportRouteProvenance, _routeSeal, provenancePkg, namePkg⟩ := carrier
  have sealDeterminacy :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealDeterminacy.right routeUnary endpointRouteConsumer
  exact
    ⟨sealDeterminacy.left, sourceUnary, witnessUnary, windowUnary, normalizerUnary,
      tailUnary, dyadicUnary, readbackUnary, sealUnary, transportUnary, routeUnary,
      provenanceUnary, nameUnary, sealDeterminacy.right, consumerUnary,
      witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
      endpointRouteConsumer, provenancePkg, namePkg, endpointPkg, consumerPkg⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_source_triad_exactness
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle consumer pkg ->
            SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                    dyadic readback sealRow transport route provenance name bundle pkg ∧
                  hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                  Cont dyadic readback sealRow ∧
                    hsame (append dyadic (append readback transport)) row ∧
                      PkgSig bundle consumer pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sealTransportEndpoint _endpointRouteConsumer consumerPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, sealUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  have triadEndpoint : hsame (append dyadic (append readback transport)) endpoint := by
    cases transportEmpty
    cases dyadicReadbackSeal
    cases sealTransportEndpoint
    exact (append_assoc dyadic readback BHist.Empty).symm
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right, unary_transport endpointUnary (hsame_symm sourceRow.right)⟩
    ledger_sound := by
      intro row sourceRow
      exact
        ⟨witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal,
          hsame_trans triadEndpoint (hsame_symm sourceRow.right), consumerPkg⟩
  }

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
