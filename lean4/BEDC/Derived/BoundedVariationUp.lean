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

theorem BoundedVariationCarrier_partition_scope_binding [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edgeRead sumRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont endpoint dyadic edgeRead ->
        Cont variation refinement sumRead ->
          UnaryHistory interval ∧ UnaryHistory partition ∧ UnaryHistory endpoint ∧
            UnaryHistory dyadic ∧ UnaryHistory variation ∧ UnaryHistory refinement ∧
              UnaryHistory edgeRead ∧ UnaryHistory sumRead ∧
                Cont interval partition endpoint ∧ Cont endpoint dyadic edgeRead ∧
                  Cont variation refinement sumRead ∧
                    hsame variation (append partition dyadic) ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier edgeReadRow sumReadRow
  obtain ⟨intervalUnary, partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, variationSame, pkgSig⟩ := carrier
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary dyadicUnary edgeReadRow
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed variationUnary refinementUnary sumReadRow
  exact
    ⟨intervalUnary, partitionUnary, endpointUnary, dyadicUnary, variationUnary,
      refinementUnary, edgeReadUnary, sumReadUnary, intervalPartitionEndpoint, edgeReadRow,
      sumReadRow, variationSame, pkgSig⟩

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

theorem BoundedVariationCarrier_transport [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      interval' partition' endpoint' dyadic' variation' refinement' transport' route' provenance'
      nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      hsame interval interval' ->
        hsame partition partition' ->
          hsame endpoint endpoint' ->
            hsame dyadic dyadic' ->
              hsame refinement refinement' ->
                hsame provenance provenance' ->
                  Cont interval' partition' endpoint' ->
                    Cont endpoint' dyadic' transport' ->
                      Cont partition' dyadic' variation' ->
                        Cont variation' refinement' route' ->
                          Cont route' provenance' nameCert' ->
                            PkgSig bundle provenance' pkg ->
                              BoundedVariationCarrier interval' partition' endpoint' dyadic'
                                  variation' refinement' transport' route' provenance'
                                  nameCert' bundle pkg ∧
                                hsame variation variation' ∧ hsame transport transport' ∧
                                  hsame route route' ∧ hsame nameCert nameCert' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameInterval samePartition sameEndpoint sameDyadic sameRefinement
    sameProvenance intervalRoute' transportRoute' variationRoute' routeRoute'
    nameCertRoute' provenancePkg'
  obtain ⟨intervalUnary, partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    refinementUnary, transportUnary, routeUnary, provenanceUnary, nameCertUnary,
    intervalRoute, transportRoute, variationRoute, routeRoute, nameCertRoute,
    variationSameAppend, _provenancePkg⟩ := carrier
  have intervalUnary' : UnaryHistory interval' :=
    unary_transport intervalUnary sameInterval
  have partitionUnary' : UnaryHistory partition' :=
    unary_transport partitionUnary samePartition
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have refinementUnary' : UnaryHistory refinement' :=
    unary_transport refinementUnary sameRefinement
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have variationSame : hsame variation variation' :=
    cont_respects_hsame samePartition sameDyadic variationRoute variationRoute'
  have transportSame : hsame transport transport' :=
    cont_respects_hsame sameEndpoint sameDyadic transportRoute transportRoute'
  have routeSame : hsame route route' :=
    cont_respects_hsame variationSame sameRefinement routeRoute routeRoute'
  have nameCertSame : hsame nameCert nameCert' :=
    cont_respects_hsame routeSame sameProvenance nameCertRoute nameCertRoute'
  have variationUnary' : UnaryHistory variation' :=
    unary_cont_closed partitionUnary' dyadicUnary' variationRoute'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed endpointUnary' dyadicUnary' transportRoute'
  have routeUnary' : UnaryHistory route' :=
    unary_cont_closed variationUnary' refinementUnary' routeRoute'
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_cont_closed routeUnary' provenanceUnary' nameCertRoute'
  have variationSameAppend' : hsame variation' (append partition' dyadic') :=
    cont_respects_hsame (hsame_refl partition') (hsame_refl dyadic') variationRoute'
      (cont_intro (hsame_refl (append partition' dyadic')))
  exact
    ⟨⟨intervalUnary', partitionUnary', endpointUnary', dyadicUnary', variationUnary',
        refinementUnary', transportUnary', routeUnary', provenanceUnary', nameCertUnary',
        intervalRoute', transportRoute', variationRoute', routeRoute', nameCertRoute',
        variationSameAppend', provenancePkg'⟩,
      variationSame, transportSame, routeSame, nameCertSame⟩

def BoundedVariationPartitionLedger [AskSetup] [PackageSetup]
    (interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory partition ∧ UnaryHistory edge ∧
    UnaryHistory endpoint ∧ UnaryHistory dyadic ∧ UnaryHistory variation ∧
      UnaryHistory refinement ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont interval partition endpoint ∧
          Cont endpoint dyadic edge ∧ Cont edge refinement variation ∧
            Cont variation transport route ∧ Cont route provenance nameCert ∧
              hsame variation (append edge refinement) ∧ PkgSig bundle provenance pkg

theorem BoundedVariationPartitionLedger_refinement_monotonicity [AskSetup] [PackageSetup]
    {interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert partition' edge' variation' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval partition edge endpoint dyadic variation refinement
        transport route provenance nameCert bundle pkg ->
      hsame partition partition' ->
        Cont endpoint dyadic edge' ->
          Cont edge' refinement variation' ->
            hsame variation variation' ∧ UnaryHistory edge' ∧ UnaryHistory variation' ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro ledger _samePartition endpointDyadicEdge' edgeRefinementVariation'
  obtain ⟨_intervalUnary, _partitionUnary, edgeUnary, endpointUnary, dyadicUnary,
    _variationUnary, refinementUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _intervalEndpoint, endpointDyadicEdge, edgeRefinementVariation,
    _variationTransportRoute, _routeProvenanceNameCert, _variationSameAppend, provenancePkg⟩ :=
      ledger
  have edgeUnary' : UnaryHistory edge' :=
    unary_cont_closed endpointUnary dyadicUnary endpointDyadicEdge'
  have sameEdge : hsame edge edge' :=
    cont_respects_hsame (hsame_refl endpoint) (hsame_refl dyadic) endpointDyadicEdge
      endpointDyadicEdge'
  have sameVariation : hsame variation variation' :=
    cont_respects_hsame sameEdge (hsame_refl refinement) edgeRefinementVariation
      edgeRefinementVariation'
  have variationUnary' : UnaryHistory variation' :=
    unary_cont_closed edgeUnary' refinementUnary edgeRefinementVariation'
  exact ⟨sameVariation, edgeUnary', variationUnary', provenancePkg⟩

theorem BoundedVariationPartitionLedger_endpoint_transport_scope [AskSetup] [PackageSetup]
    {interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert endpoint' edge' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval partition edge endpoint dyadic variation refinement
        transport route provenance nameCert bundle pkg ->
      hsame endpoint endpoint' ->
        Cont endpoint' dyadic edge' ->
          UnaryHistory endpoint' ∧ UnaryHistory edge' ∧ hsame edge edge' ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro ledger sameEndpoint endpointDyadicEdge'
  obtain ⟨_intervalUnary, _partitionUnary, _edgeUnary, endpointUnary, dyadicUnary,
    _variationUnary, _refinementUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _intervalPartitionEndpoint, endpointDyadicEdge, _edgeRefinementVariation,
    _variationTransportRoute, _routeProvenanceNameCert, _variationSameAppend,
    provenancePkg⟩ := ledger
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have edgeUnary' : UnaryHistory edge' :=
    unary_cont_closed endpointUnary' dyadicUnary endpointDyadicEdge'
  have sameEdge : hsame edge edge' :=
    cont_respects_hsame sameEndpoint (hsame_refl dyadic) endpointDyadicEdge endpointDyadicEdge'
  exact ⟨endpointUnary', edgeUnary', sameEdge, provenancePkg⟩

theorem BoundedVariationPartitionLedger_concatenation_ledger [AskSetup] [PackageSetup]
    {interval0 partition0 edge0 endpoint0 dyadic0 variation0 refinement0 transport0 route0
      provenance0 nameCert0 interval1 partition1 edge1 endpoint1 dyadic1 variation1 refinement1
      transport1 route1 provenance1 nameCert1 variation01 route01 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval0 partition0 edge0 endpoint0 dyadic0 variation0
        refinement0 transport0 route0 provenance0 nameCert0 bundle pkg ->
      BoundedVariationPartitionLedger interval1 partition1 edge1 endpoint1 dyadic1 variation1
          refinement1 transport1 route1 provenance1 nameCert1 bundle pkg ->
        hsame endpoint0 endpoint1 ->
          Cont variation0 variation1 variation01 ->
            Cont route0 route1 route01 ->
              UnaryHistory variation01 ∧ UnaryHistory route01 ∧ hsame endpoint0 endpoint1 ∧
                PkgSig bundle provenance0 pkg ∧ PkgSig bundle provenance1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro ledger0 ledger1 sameEndpoint variationConcat routeConcat
  obtain ⟨_intervalUnary0, _partitionUnary0, _edgeUnary0, _endpointUnary0, _dyadicUnary0,
    variationUnary0, _refinementUnary0, _transportUnary0, routeUnary0, _provenanceUnary0,
    _nameCertUnary0, _intervalEndpoint0, _endpointDyadicEdge0, _edgeRefinementVariation0,
    _variationTransportRoute0, _routeProvenanceNameCert0, _variationSameAppend0,
    provenancePkg0⟩ := ledger0
  obtain ⟨_intervalUnary1, _partitionUnary1, _edgeUnary1, _endpointUnary1, _dyadicUnary1,
    variationUnary1, _refinementUnary1, _transportUnary1, routeUnary1, _provenanceUnary1,
    _nameCertUnary1, _intervalEndpoint1, _endpointDyadicEdge1, _edgeRefinementVariation1,
    _variationTransportRoute1, _routeProvenanceNameCert1, _variationSameAppend1,
    provenancePkg1⟩ := ledger1
  have variationUnary01 : UnaryHistory variation01 :=
    unary_cont_closed variationUnary0 variationUnary1 variationConcat
  have routeUnary01 : UnaryHistory route01 :=
    unary_cont_closed routeUnary0 routeUnary1 routeConcat
  exact ⟨variationUnary01, routeUnary01, sameEndpoint, provenancePkg0, provenancePkg1⟩

theorem BoundedVariationPartitionLedger_refinement_additivity_scope [AskSetup] [PackageSetup]
    {interval partition edge endpoint dyadic variation refinement transport route provenance
      nameCert edge' variation' blockSum : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationPartitionLedger interval partition edge endpoint dyadic variation refinement
        transport route provenance nameCert bundle pkg ->
      Cont endpoint dyadic edge' ->
        Cont edge' refinement variation' ->
          Cont variation' transport blockSum ->
            PkgSig bundle blockSum pkg ->
              hsame variation variation' ∧ UnaryHistory edge' ∧ UnaryHistory variation' ∧
                UnaryHistory blockSum ∧ Cont variation' transport blockSum ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle blockSum pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro ledger endpointDyadicEdge' edgeRefinementVariation' variationTransportBlock blockPkg
  obtain ⟨_intervalUnary, _partitionUnary, _edgeUnary, endpointUnary, dyadicUnary,
    _variationUnary, refinementUnary, transportUnary, _routeUnary, _provenanceUnary,
    _nameCertUnary, _intervalPartitionEndpoint, endpointDyadicEdge, edgeRefinementVariation,
    _variationTransportRoute, _routeProvenanceNameCert, _variationSameAppend,
    provenancePkg⟩ := ledger
  have edgeUnary' : UnaryHistory edge' :=
    unary_cont_closed endpointUnary dyadicUnary endpointDyadicEdge'
  have sameEdge : hsame edge edge' :=
    cont_respects_hsame (hsame_refl endpoint) (hsame_refl dyadic) endpointDyadicEdge
      endpointDyadicEdge'
  have sameVariation : hsame variation variation' :=
    cont_respects_hsame sameEdge (hsame_refl refinement) edgeRefinementVariation
      edgeRefinementVariation'
  have variationUnary' : UnaryHistory variation' :=
    unary_cont_closed edgeUnary' refinementUnary edgeRefinementVariation'
  have blockSumUnary : UnaryHistory blockSum :=
    unary_cont_closed variationUnary' transportUnary variationTransportBlock
  exact
    ⟨sameVariation, edgeUnary', variationUnary', blockSumUnary, variationTransportBlock,
      provenancePkg, blockPkg⟩

theorem BoundedVariationCarrier_cauchy_consumer_boundary [AskSetup] [PackageSetup]
    {interval partition endpoint dyadic variation refinement transport route provenance nameCert
      edgeRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedVariationCarrier interval partition endpoint dyadic variation refinement transport route
        provenance nameCert bundle pkg ->
      Cont endpoint dyadic edgeRead ->
        Cont variation refinement cauchyRead ->
          PkgSig bundle cauchyRead pkg ->
            UnaryHistory endpoint ∧ UnaryHistory dyadic ∧ UnaryHistory variation ∧
              UnaryHistory edgeRead ∧ UnaryHistory cauchyRead ∧
                Cont endpoint dyadic edgeRead ∧ Cont variation refinement cauchyRead ∧
                  hsame variation (append partition dyadic) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier endpointDyadicEdgeRead variationRefinementCauchy cauchyPkg
  obtain ⟨_intervalUnary, _partitionUnary, endpointUnary, dyadicUnary, variationUnary,
    refinementUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary,
    _intervalPartitionEndpoint, _endpointDyadicTransport, _partitionDyadicVariation,
    _variationRefinementRoute, _routeProvenanceNameCert, variationSame, provenancePkg⟩ :=
      carrier
  have edgeReadUnary : UnaryHistory edgeRead :=
    unary_cont_closed endpointUnary dyadicUnary endpointDyadicEdgeRead
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed variationUnary refinementUnary variationRefinementCauchy
  exact
    ⟨endpointUnary, dyadicUnary, variationUnary, edgeReadUnary, cauchyReadUnary,
      endpointDyadicEdgeRead, variationRefinementCauchy, variationSame, provenancePkg,
      cauchyPkg⟩

end BEDC.Derived.BoundedVariationUp
