import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactModulusCoverCarrier [AskSetup] [PackageSetup]
    (compactSource continuousRow tolerance bundleRow coverRows pointwiseRows handoff radiusFamily
      transports routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory compactSource ∧ UnaryHistory continuousRow ∧ UnaryHistory tolerance ∧
    UnaryHistory bundleRow ∧ UnaryHistory coverRows ∧ UnaryHistory pointwiseRows ∧
      UnaryHistory handoff ∧ UnaryHistory radiusFamily ∧ UnaryHistory transports ∧
        UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
          Cont compactSource bundleRow coverRows ∧ Cont continuousRow tolerance pointwiseRows ∧
            Cont pointwiseRows radiusFamily handoff ∧ Cont handoff transports routes ∧
              Cont routes provenance localCert ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localCert pkg

theorem CompactModulusCoverCarrier_finite_net_source_exhaustion [AskSetup] [PackageSetup]
    {compactSource continuousRow tolerance bundleRow coverRows pointwiseRows handoff radiusFamily
      transports routes provenance localCert coverRead pointwiseRead foldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactModulusCoverCarrier compactSource continuousRow tolerance bundleRow coverRows
        pointwiseRows handoff radiusFamily transports routes provenance localCert bundle pkg ->
      Cont compactSource bundleRow coverRead ->
        Cont continuousRow tolerance pointwiseRead ->
          Cont pointwiseRows radiusFamily foldRead ->
            UnaryHistory coverRead ∧ UnaryHistory pointwiseRead ∧ UnaryHistory foldRead ∧
              PkgSig bundle provenance pkg := by
  intro carrier coverReadRow pointwiseReadRow foldReadRow
  obtain ⟨compactSourceUnary, continuousRowUnary, toleranceUnary, bundleRowUnary,
    _coverRowsUnary, pointwiseRowsUnary, _handoffUnary, radiusFamilyUnary, _transportsUnary,
    _routesUnary, _provenanceUnary, _localCertUnary, _compactRoute, _pointwiseRoute,
    _handoffRoute, _routesTransport, _localCertRoute, provenancePkg, _localCertPkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactSourceUnary bundleRowUnary coverReadRow
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed continuousRowUnary toleranceUnary pointwiseReadRow
  have foldReadUnary : UnaryHistory foldRead :=
    unary_cont_closed pointwiseRowsUnary radiusFamilyUnary foldReadRow
  exact ⟨coverReadUnary, pointwiseReadUnary, foldReadUnary, provenancePkg⟩

theorem CompactModulusCoverCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {compactSource continuousRow tolerance bundleRow coverRows pointwiseRows handoff radiusFamily
      transports routes provenance localCert handoffRead uniformRead foldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactModulusCoverCarrier compactSource continuousRow tolerance bundleRow coverRows
        pointwiseRows handoff radiusFamily transports routes provenance localCert bundle pkg ->
      Cont pointwiseRows radiusFamily handoffRead ->
        Cont handoff transports uniformRead ->
          Cont pointwiseRows radiusFamily foldRead ->
            UnaryHistory handoffRead ∧ UnaryHistory uniformRead ∧ UnaryHistory foldRead ∧
              Cont handoff transports routes ∧ PkgSig bundle localCert pkg := by
  intro carrier handoffReadRow uniformReadRow foldReadRow
  obtain ⟨_compactSourceUnary, _continuousRowUnary, _toleranceUnary, _bundleRowUnary,
    _coverRowsUnary, pointwiseRowsUnary, _handoffUnary, radiusFamilyUnary, transportsUnary,
    _routesUnary, _provenanceUnary, _localCertUnary, _compactRoute, _pointwiseRoute,
    _handoffRoute, handoffTransportRoute, _localCertRoute, _provenancePkg, localCertPkg⟩ :=
    carrier
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed pointwiseRowsUnary radiusFamilyUnary handoffReadRow
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed _handoffUnary transportsUnary uniformReadRow
  have foldReadUnary : UnaryHistory foldRead :=
    unary_cont_closed pointwiseRowsUnary radiusFamilyUnary foldReadRow
  exact ⟨handoffReadUnary, uniformReadUnary, foldReadUnary, handoffTransportRoute, localCertPkg⟩

theorem CompactModulusCoverCarrier_obligation_triad [AskSetup] [PackageSetup]
    {compactSource continuousRow tolerance bundleRow coverRows pointwiseRows handoff radiusFamily
      transports routes provenance localCert coverRead pointwiseRead handoffRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactModulusCoverCarrier compactSource continuousRow tolerance bundleRow coverRows
        pointwiseRows handoff radiusFamily transports routes provenance localCert bundle pkg ->
      Cont compactSource bundleRow coverRead ->
        Cont continuousRow tolerance pointwiseRead ->
          Cont pointwiseRows radiusFamily handoffRead ->
            Cont handoff transports uniformRead ->
              UnaryHistory coverRead ∧ UnaryHistory pointwiseRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory uniformRead ∧ Cont routes provenance localCert ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg := by
  intro carrier coverReadRow pointwiseReadRow handoffReadRow uniformReadRow
  obtain ⟨compactSourceUnary, continuousRowUnary, toleranceUnary, bundleRowUnary,
    _coverRowsUnary, pointwiseRowsUnary, handoffUnary, radiusFamilyUnary, transportsUnary,
    _routesUnary, _provenanceUnary, _localCertUnary, _compactRoute, _pointwiseRoute,
    _handoffRoute, _handoffTransportRoute, routesProvenanceLocalCert, provenancePkg,
    localCertPkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactSourceUnary bundleRowUnary coverReadRow
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed continuousRowUnary toleranceUnary pointwiseReadRow
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed pointwiseRowsUnary radiusFamilyUnary handoffReadRow
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed handoffUnary transportsUnary uniformReadRow
  exact ⟨coverReadUnary, pointwiseReadUnary, handoffReadUnary, uniformReadUnary,
    routesProvenanceLocalCert, provenancePkg, localCertPkg⟩

theorem CompactModulusCoverCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactSource continuousRow tolerance bundleRow coverRows pointwiseRows handoff radiusFamily
      transports routes provenance localCert coverRead pointwiseRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactModulusCoverCarrier compactSource continuousRow tolerance bundleRow coverRows
        pointwiseRows handoff radiusFamily transports routes provenance localCert bundle pkg ->
      Cont compactSource bundleRow coverRead ->
        Cont continuousRow tolerance pointwiseRead ->
          Cont routes provenance routeRead ->
            UnaryHistory coverRead ∧ UnaryHistory pointwiseRead ∧ UnaryHistory routeRead ∧
              Cont pointwiseRows radiusFamily handoff ∧ PkgSig bundle localCert pkg := by
  intro carrier coverReadRow pointwiseReadRow routeReadRow
  obtain ⟨compactSourceUnary, continuousRowUnary, toleranceUnary, bundleRowUnary,
    _coverRowsUnary, pointwiseRowsUnary, _handoffUnary, radiusFamilyUnary, _transportsUnary,
    routesUnary, provenanceUnary, _localCertUnary, _compactRoute, _pointwiseRoute,
    handoffRoute, _routesTransport, _localCertRoute, _provenancePkg, localCertPkg⟩ := carrier
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed compactSourceUnary bundleRowUnary coverReadRow
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed continuousRowUnary toleranceUnary pointwiseReadRow
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed routesUnary provenanceUnary routeReadRow
  exact ⟨coverReadUnary, pointwiseReadUnary, routeReadUnary, handoffRoute, localCertPkg⟩

end BEDC.Derived.CompactModulusCoverUp
