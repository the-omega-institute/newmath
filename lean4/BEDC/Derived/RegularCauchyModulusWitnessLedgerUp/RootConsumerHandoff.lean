import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
