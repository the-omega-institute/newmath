import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RegularCauchyModulusWitnessLedgerCarrier_root_exit_partition_stability
    [AskSetup] [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance name
      endpoint endpoint' consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont sealRow transport endpoint' ->
          Cont endpoint route consumer ->
            Cont endpoint' route consumer' ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle consumer' pkg ->
                  hsame endpoint endpoint' /\ hsame consumer consumer' /\ hsame route sealRow /\
                    Cont witness window normalizer /\ Cont normalizer tail dyadic /\
                      Cont dyadic readback sealRow /\ Cont endpoint route consumer /\
                        Cont endpoint' route consumer' /\ PkgSig bundle consumer pkg /\
                          PkgSig bundle consumer' pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame
  intro carrier sealTransportEndpoint sealTransportEndpoint' endpointRouteConsumer
    endpointRouteConsumer' consumerPkg consumerPkg'
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, _windowUnary, _normalizerUnary, _tailUnary,
    _dyadicUnary, _readbackUnary, _sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have endpointDet :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint) carrierWitness
      sealTransportEndpoint
  have endpointDet' :=
    RegularCauchyModulusWitnessLedgerCarrier_seal_route_determinacy
      (source := source) (witness := witness) (window := window)
      (normalizer := normalizer) (tail := tail) (dyadic := dyadic)
      (readback := readback) (sealRow := sealRow) (transport := transport)
      (route := route) (provenance := provenance) (name := name)
      (bundle := bundle) (pkg := pkg) (endpoint := endpoint') carrierWitness
      sealTransportEndpoint'
  have endpointSame : hsame endpoint endpoint' :=
    hsame_trans endpointDet.left (hsame_symm endpointDet'.left)
  have consumerSame : hsame consumer consumer' :=
    cont_respects_hsame endpointSame (hsame_refl route) endpointRouteConsumer
      endpointRouteConsumer'
  exact
    ⟨endpointSame, consumerSame, routeSeal, witnessWindowNormalizer, normalizerTailDyadic,
      dyadicReadbackSeal, endpointRouteConsumer, endpointRouteConsumer', consumerPkg,
      consumerPkg'⟩

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
