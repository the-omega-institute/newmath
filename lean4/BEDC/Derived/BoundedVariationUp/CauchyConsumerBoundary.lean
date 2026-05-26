import BEDC.Derived.BoundedVariationUp

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedVariationCauchyConsumerBoundary [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edgeRead variationRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont endpoint dyadic edgeRead ->
        Cont edgeRead variation variationRead ->
          Cont variationRead nameCert consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory edgeRead ∧ UnaryHistory variationRead ∧ UnaryHistory consumerRead ∧
                Cont endpoint dyadic edgeRead ∧ Cont edgeRead variation variationRead ∧
                  Cont variationRead nameCert consumerRead ∧
                    hsame variation (append partition dyadic) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier endpointDyadicEdgeRead edgeReadVariationVariationRead
    variationReadNameCertConsumerRead consumerPkg
  obtain ⟨_intervalUnary, _partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, variationSame, provenancePkg⟩ :=
      carrier
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary dyadicUnary endpointDyadicEdgeRead
  have variationReadUnary : UnaryHistory variationRead :=
    unary_cont_closed edgeReadUnary variationUnary edgeReadVariationVariationRead
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed variationReadUnary nameCertUnary variationReadNameCertConsumerRead
  exact
    ⟨edgeReadUnary, variationReadUnary, consumerReadUnary, endpointDyadicEdgeRead,
      edgeReadVariationVariationRead, variationReadNameCertConsumerRead, variationSame,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.BoundedVariationUp
