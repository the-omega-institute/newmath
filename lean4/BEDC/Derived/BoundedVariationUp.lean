import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedVariationCarrier [AskSetup] [PackageSetup]
    (interval partition endpoint dyadic variation refinement transport route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory partition ∧ UnaryHistory endpoint ∧
    UnaryHistory dyadic ∧ UnaryHistory variation ∧ UnaryHistory refinement ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont interval partition endpoint ∧
          Cont endpoint dyadic transport ∧ Cont partition dyadic variation ∧
            Cont variation refinement route ∧ Cont route provenance nameCert ∧
              hsame variation (append partition dyadic) ∧ PkgSig bundle provenance pkg

theorem BoundedVariationCarrier_variation_ledger_exactness [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edgeRead sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont endpoint dyadic edgeRead ->
        Cont variation refinement sumRead ->
          UnaryHistory edgeRead ∧ UnaryHistory sumRead ∧
            hsame variation (append partition dyadic) ∧ PkgSig bundle provenance pkg := by
  intro carrier edgeReadRow sumReadRow
  obtain ⟨_intervalUnary, _partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, variationSame, pkgSig⟩ := carrier
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary dyadicUnary edgeReadRow
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed variationUnary refinementUnary sumReadRow
  exact ⟨edgeReadUnary, sumReadUnary, variationSame, pkgSig⟩

end BEDC.Derived.BoundedVariationUp
