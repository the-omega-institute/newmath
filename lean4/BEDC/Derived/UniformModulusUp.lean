import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformModulusPacket [AskSetup] [PackageSetup]
    (tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
    UnaryHistory radius ∧ UnaryHistory nameRow ∧
      Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport ∧
        Cont precision radius foldLedger ∧ Cont foldLedger nameRow provenance ∧
          PkgSig bundle provenance pkg

theorem UniformModulusPacket_finite_probe_bundle_fold [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow foldedExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont precision radius foldLedger ->
        Cont foldLedger nameRow foldedExport ->
          PkgSig bundle foldedExport pkg ->
            UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
              UnaryHistory radius ∧ UnaryHistory foldLedger ∧ UnaryHistory foldedExport ∧
                Cont precision radius foldLedger ∧ Cont foldLedger nameRow foldedExport ∧
                  PkgSig bundle foldedExport pkg := by
  intro packet foldRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, _packetFoldRoute, _provenanceRoute, _provenancePkg⟩ :=
    packet
  have foldUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have exportUnary : UnaryHistory foldedExport :=
    unary_cont_closed foldUnary nameRowUnary exportRoute
  exact
    ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, foldUnary, exportUnary,
      foldRoute, exportRoute, exportPkg⟩

theorem UniformModulusPacket_compact_metric_source_lock [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont bundleRow radius compactRead ->
        Cont compactRead coverage transport ->
          PkgSig bundle provenance pkg ->
            UnaryHistory bundleRow ∧ UnaryHistory radius ∧
              Cont bundleRow radius compactRead ∧ Cont compactRead coverage transport ∧
                PkgSig bundle provenance pkg := by
  intro packet compactRoute coverageRoute provenancePkg
  obtain ⟨_toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    _coverageRoute, _transportRoute, _packetFoldRoute, _provenanceRoute, _packetPkg⟩ :=
    packet
  exact ⟨bundleRowUnary, radiusUnary, compactRoute, coverageRoute, provenancePkg⟩

theorem UniformModulusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont foldLedger nameRow exported ->
        PkgSig bundle exported pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont foldLedger nameRow row ∧
              Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport)
            (fun row : BHist => PkgSig bundle row pkg ∧ Cont precision radius foldLedger ∧
              Cont foldLedger nameRow exported)
            (fun row row' : BHist => hsame row row') := by
  intro packet exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    toleranceBundleCoverage, coveragePointwiseTransport, precisionRadiusFoldLedger,
    _foldNameProvenance, _provenancePkg⟩ := packet
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed foldLedgerUnary nameRowUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
          toleranceBundleCoverage, coveragePointwiseTransport⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, precisionRadiusFoldLedger, exportRoute⟩
  }

theorem UniformModulusPacket_root_unblock_consumer_threshold_route [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow threshold exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      Cont tolerance precision threshold →
        Cont threshold foldLedger exported →
          PkgSig bundle exported pkg →
            SemanticNameCert
              (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont threshold foldLedger row ∧
                Cont tolerance precision threshold ∧ Cont precision radius foldLedger)
              (fun row : BHist => PkgSig bundle row pkg ∧
                Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport)
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet thresholdRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    toleranceBundleCoverage, coveragePointwiseTransport, precisionRadiusFoldLedger,
    _foldNameProvenance, _provenancePkg⟩ := packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed toleranceUnary precisionUnary thresholdRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed thresholdUnary foldLedgerUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
          thresholdRoute, precisionRadiusFoldLedger⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, toleranceBundleCoverage, coveragePointwiseTransport⟩
  }

theorem UniformModulusPacket_classifier_transport_stability [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow tolerance' precision' bundleRow' radius' coverage' pointwise' foldLedger'
      transport' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      hsame tolerance tolerance' -> hsame precision precision' -> hsame bundleRow bundleRow' ->
        hsame radius radius' -> hsame nameRow nameRow' ->
          Cont tolerance' bundleRow' coverage' -> Cont coverage' pointwise' transport' ->
            Cont precision' radius' foldLedger' -> Cont foldLedger' nameRow' provenance' ->
              PkgSig bundle provenance' pkg ->
                UniformModulusPacket tolerance' precision' bundleRow' radius' coverage'
                  pointwise' foldLedger' transport' provenance' nameRow' bundle pkg /\
                    hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro packet sameTolerance samePrecision sameBundleRow sameRadius sameNameRow
    coverageRoute' transportRoute' foldRoute' provenanceRoute' provenancePkg'
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    coverageRoute, _transportRoute, foldRoute, provenanceRoute, _provenancePkg⟩ := packet
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have bundleRowUnary' : UnaryHistory bundleRow' :=
    unary_transport bundleRowUnary sameBundleRow
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have nameRowUnary' : UnaryHistory nameRow' :=
    unary_transport nameRowUnary sameNameRow
  have sameFoldLedger : hsame foldLedger foldLedger' :=
    cont_respects_hsame samePrecision sameRadius foldRoute foldRoute'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameFoldLedger sameNameRow provenanceRoute provenanceRoute'
  exact
    ⟨⟨toleranceUnary',
      precisionUnary',
      bundleRowUnary',
      radiusUnary',
      nameRowUnary',
      coverageRoute',
      transportRoute',
      foldRoute',
      provenanceRoute',
      provenancePkg'⟩,
      sameProvenance⟩

theorem UniformModulusPacket_covered_point_radius_route [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow distance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      UnaryHistory pointwise →
        Cont coverage pointwise distance →
          Cont distance foldLedger consumer →
            PkgSig bundle consumer pkg →
              UnaryHistory coverage ∧ UnaryHistory foldLedger ∧ UnaryHistory distance ∧
                UnaryHistory consumer ∧ Cont coverage pointwise distance ∧
                  Cont distance foldLedger consumer ∧ Cont precision radius foldLedger ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro packet pointwiseUnary coveragePointwiseDistance distanceFoldConsumer consumerPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    toleranceBundleCoverage, _coveragePointwiseTransport, precisionRadiusFoldLedger,
    _foldNameProvenance, _provenancePkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary toleranceBundleCoverage
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed coverageUnary pointwiseUnary coveragePointwiseDistance
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed distanceUnary foldLedgerUnary distanceFoldConsumer
  exact
    ⟨coverageUnary, foldLedgerUnary, distanceUnary, consumerUnary,
      coveragePointwiseDistance, distanceFoldConsumer, precisionRadiusFoldLedger, consumerPkg⟩

theorem UniformModulusPacket_finite_net_realizer_unblock [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow realized : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont tolerance bundleRow coverage ->
        Cont precision radius foldLedger ->
          Cont foldLedger nameRow realized ->
            PkgSig bundle realized pkg ->
              UnaryHistory tolerance ∧ UnaryHistory bundleRow ∧ UnaryHistory radius ∧
                UnaryHistory coverage ∧ UnaryHistory foldLedger ∧ UnaryHistory realized ∧
                  Cont tolerance bundleRow coverage ∧ Cont precision radius foldLedger ∧
                    Cont foldLedger nameRow realized ∧ PkgSig bundle realized pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro packet coverageRoute foldRoute realizedRoute realizedPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _packetCoverageRoute, _packetTransportRoute, _packetFoldRoute, _packetProvenanceRoute,
    _packetPkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have foldUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have realizedUnary : UnaryHistory realized :=
    unary_cont_closed foldUnary nameRowUnary realizedRoute
  exact
    ⟨toleranceUnary, bundleRowUnary, radiusUnary, coverageUnary, foldUnary, realizedUnary,
      coverageRoute, foldRoute, realizedRoute, realizedPkg⟩

theorem UniformModulusPacket_root_compact_cover_row_totality [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      Cont bundleRow radius compactRead →
        Cont compactRead coverage boundary →
          PkgSig bundle boundary pkg →
            UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory compactRead ∧
              UnaryHistory boundary ∧ Cont bundleRow radius compactRead ∧
                Cont compactRead coverage boundary ∧ PkgSig bundle boundary pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet bundleRadiusCompactRead compactReadCoverageBoundary boundaryPkg
  obtain ⟨toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    toleranceBundleCoverage, _coveragePointwiseTransport, _precisionRadiusFoldLedger,
    _foldNameProvenance, _provenancePkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary toleranceBundleCoverage
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompactRead
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed compactReadUnary coverageUnary compactReadCoverageBoundary
  exact
    ⟨bundleRowUnary, radiusUnary, compactReadUnary, boundaryUnary,
      bundleRadiusCompactRead, compactReadCoverageBoundary, boundaryPkg⟩

theorem UniformModulusPacket_root_pointwise_modulus_row_totality [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead transport consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory compactRead ∧
                  UnaryHistory pointwiseRead ∧ UnaryHistory transport ∧
                    UnaryHistory consumer ∧ Cont bundleRow radius compactRead ∧
                      Cont compactRead pointwise pointwiseRead ∧
                        Cont pointwiseRead transport consumer ∧
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro packet pointwiseUnary compactRoute pointwiseRoute consumerRoute consumerPkg
  obtain ⟨toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, _nameRowUnary,
    coverageRoute, transportRoute, _packetFoldRoute, _provenanceRoute, _provenancePkg⟩ :=
    packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed coverageUnary pointwiseUnary transportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed pointwiseReadUnary transportUnary consumerRoute
  exact
    ⟨bundleRowUnary, radiusUnary, compactReadUnary, pointwiseReadUnary, transportUnary,
      consumerUnary, compactRoute, pointwiseRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.UniformModulusUp
