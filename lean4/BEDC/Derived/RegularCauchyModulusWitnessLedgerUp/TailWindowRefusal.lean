import BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusWitnessLedgerCarrier_tail_window_refusal [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        Cont endpoint route consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory window ∧ UnaryHistory tail ∧ UnaryHistory dyadic ∧
              UnaryHistory readback ∧ Cont witness window normalizer ∧
                Cont normalizer tail dyadic ∧ Cont dyadic readback sealRow ∧
                  hsame endpoint sealRow ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier sealTransportEndpoint _endpointRouteConsumer consumerPkg
  have carrierWitness :
      RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    dyadicUnary, readbackUnary, _sealUnary, _transportUnary, _routeUnary,
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
  exact
    ⟨windowUnary, tailUnary, dyadicUnary, readbackUnary, witnessWindowNormalizer,
      normalizerTailDyadic, dyadicReadbackSeal, sealDeterminacy.left, consumerPkg⟩

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
