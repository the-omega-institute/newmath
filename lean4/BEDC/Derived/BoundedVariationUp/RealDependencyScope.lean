import BEDC.Derived.BoundedVariationUp

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedVariationCarrier_real_dependency_scope [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      endpointRead realRead dyadicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont interval partition endpointRead ->
        Cont endpointRead endpoint realRead ->
          Cont realRead dyadic dyadicRead ->
            PkgSig bundle dyadicRead pkg ->
              UnaryHistory endpointRead ∧ UnaryHistory realRead ∧
                UnaryHistory dyadicRead ∧ Cont interval partition endpointRead ∧
                  Cont endpointRead endpoint realRead ∧ Cont realRead dyadic dyadicRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle dyadicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier intervalPartitionEndpointRead endpointReadEndpointRealRead
    realReadDyadicDyadicRead dyadicPkg
  obtain ⟨intervalUnary, partitionUnary, endpointUnary, dyadicUnary, _variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, _variationSame, provenancePkg⟩ :=
      carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed intervalUnary partitionUnary intervalPartitionEndpointRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointReadUnary endpointUnary endpointReadEndpointRealRead
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed realReadUnary dyadicUnary realReadDyadicDyadicRead
  exact
    ⟨endpointReadUnary, realReadUnary, dyadicReadUnary, intervalPartitionEndpointRead,
      endpointReadEndpointRealRead, realReadDyadicDyadicRead, provenancePkg, dyadicPkg⟩

end BEDC.Derived.BoundedVariationUp
