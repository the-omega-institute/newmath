import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusWitnessLedgerCarrier_streamname_regseqrat_real_exactness
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle consumer pkg ->
            hsame endpoint sealRow ∧
              hsame (append dyadic (append readback transport)) endpoint ∧
                hsame (append endpoint route) consumer ∧ UnaryHistory window ∧
                  UnaryHistory dyadic ∧ UnaryHistory readback ∧ UnaryHistory consumer ∧
                    Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                      Cont dyadic readback sealRow ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier sealTransportEndpoint endpointRouteConsumer consumerPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, windowUnary, _normalizerUnary, _tailUnary,
    dyadicUnary, readbackUnary, _sealUnary, _transportUnary, routeUnary, _provenanceUnary,
    _nameUnary, _transportEmpty, witnessWindowNormalizer, normalizerTailDyadic,
    dyadicReadbackSeal, _transportRouteProvenance, _routeSeal, _provenancePkg,
    _namePkg⟩ := carrier
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
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealDeterminacy.right routeUnary endpointRouteConsumer
  exact
    ⟨sealDeterminacy.left, consumerExactness.left, consumerExactness.right.left, windowUnary,
      dyadicUnary, readbackUnary, consumerUnary, witnessWindowNormalizer, normalizerTailDyadic,
      dyadicReadbackSeal, consumerExactness.right.right⟩

theorem RegularCauchyModulusWitnessLedgerCarrier_tail_service_uniqueness [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint serviceRead serviceRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg →
      Cont sealRow transport endpoint →
        Cont endpoint route serviceRead →
          Cont endpoint route serviceRead' →
            PkgSig bundle serviceRead pkg →
              PkgSig bundle serviceRead' pkg →
                hsame serviceRead serviceRead' ∧ hsame endpoint sealRow ∧
                  Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                    Cont dyadic readback sealRow ∧ PkgSig bundle serviceRead pkg ∧
                      PkgSig bundle serviceRead' pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame
  intro carrier sealTransportEndpoint endpointRouteService endpointRouteService' servicePkg
    servicePkg'
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have sealDeterminacy :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have serviceSame : hsame serviceRead serviceRead' :=
    cont_respects_hsame (hsame_refl endpoint) (hsame_refl route) endpointRouteService
      endpointRouteService'
  exact
    ⟨serviceSame, sealDeterminacy.left, witnessWindowNormalizer, normalizerTailDyadic,
      dyadicReadbackSeal, servicePkg, servicePkg'⟩

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
