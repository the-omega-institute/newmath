import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem BoundedVariationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport
              route provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
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
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem BoundedVariationCarrier_public_rows_zero_head_absurd [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      zInterval zVariation zNameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      (hsame interval (BHist.e0 zInterval) -> False) ∧
        (hsame variation (BHist.e0 zVariation) -> False) ∧
          (hsame nameCert (BHist.e0 zNameCert) -> False) := by
  intro carrier
  obtain ⟨intervalUnary, _partitionUnary, _endpointUnary, _dyadicUnary, variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, _variationSame, _pkgSig⟩ := carrier
  constructor
  · intro sameIntervalZero
    exact unary_no_zero_extension (unary_transport intervalUnary sameIntervalZero)
  constructor
  · intro sameVariationZero
    exact unary_no_zero_extension (unary_transport variationUnary sameVariationZero)
  · intro sameNameCertZero
    exact unary_no_zero_extension (unary_transport nameCertUnary sameNameCertZero)

theorem BoundedVariationCarrier_common_refinement_classifier_exactness [AskSetup]
    [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      interval' partition' endpoint' dyadic' variation' refinement' transport' route' provenance'
      nameCert' edgeRead sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      BoundedVariationCarrier interval' partition' endpoint' dyadic' variation' refinement'
          transport' route' provenance' nameCert' bundle pkg ->
        hsame interval interval' ->
          hsame partition partition' ->
            hsame endpoint endpoint' ->
              hsame dyadic dyadic' ->
                hsame refinement refinement' ->
                  hsame provenance provenance' ->
                    Cont endpoint' dyadic' edgeRead ->
                      Cont variation' refinement' sumRead ->
                        PkgSig bundle sumRead pkg ->
                          UnaryHistory edgeRead ∧ UnaryHistory sumRead ∧
                            hsame variation variation' ∧ hsame transport transport' ∧
                              hsame route route' ∧ hsame provenance provenance' ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle sumRead pkg := by
  intro carrier carrier' sameInterval samePartition sameEndpoint sameDyadic
    sameRefinement sameProvenance endpointDyadicEdge variationRefinementSum sumPkg
  obtain ⟨_intervalUnary, _partitionUnary, _endpointUnary, _dyadicUnary, _variationUnary,
    _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    intervalPartitionEndpoint, endpointDyadicTransport, partitionDyadicVariation,
    variationRefinementRoute, _routeProvenanceNameCert, _variationSame, provenancePkg⟩ :=
      carrier
  obtain ⟨_intervalUnary', _partitionUnary', endpointUnary', dyadicUnary', variationUnary',
    refinementUnary', _transportUnary', _routeUnary', _provenanceUnary', _nameCertUnary',
    intervalPartitionEndpoint', endpointDyadicTransport', partitionDyadicVariation',
    variationRefinementRoute', _routeProvenanceNameCert', _variationSame',
    _provenancePkg'⟩ := carrier'
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary' dyadicUnary' endpointDyadicEdge
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed variationUnary' refinementUnary' variationRefinementSum
  have sameVariation : hsame variation variation' :=
    cont_respects_hsame samePartition sameDyadic partitionDyadicVariation
      partitionDyadicVariation'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameEndpoint sameDyadic endpointDyadicTransport endpointDyadicTransport'
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameVariation sameRefinement variationRefinementRoute
      variationRefinementRoute'
  exact
    ⟨edgeReadUnary, sumReadUnary, sameVariation, sameTransport, sameRoute, sameProvenance,
      provenancePkg, sumPkg⟩

end BEDC.Derived.BoundedVariationUp
