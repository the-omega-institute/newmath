import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactUniformContinuityPacket [AskSetup] [PackageSetup]
    (source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧ UnaryHistory tolerance ∧
    UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory radiusRows ∧
      UnaryHistory transport ∧ UnaryHistory nameRow ∧ Cont net coverage modulusRows ∧
        Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
          Cont route nameRow precision ∧ PkgSig bundle precision pkg

theorem CompactUniformContinuityPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row precision ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist => Cont route nameRow row ∧ Cont net coverage modulusRows ∧
          Cont modulusRows radiusRows fold)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont fold transport route ∧
          Cont route nameRow precision)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ := packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro precision ⟨hsame_refl precision, precisionUnary, precisionPkg⟩
      equiv_refl := by
        intro row _sourceRow
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
        ⟨cont_result_hsame_transport routeNamePrecision (hsame_symm sourceRow.left),
          netCoverageModulusRows, modulusRowsRadiusRowsFold⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, foldTransportRoute, routeNamePrecision⟩
  }

theorem CompactUniformContinuityPacket_realup_consumer_boundary [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision nameRow metricRead ->
        Cont metricRead transport realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
              UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory metricRead ∧
                UnaryHistory realRead ∧ Cont net coverage modulusRows ∧
                  Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                    Cont route nameRow precision ∧ Cont precision nameRow metricRead ∧
                      Cont metricRead transport realRead ∧ PkgSig bundle precision pkg ∧
                        PkgSig bundle realRead pkg := by
  intro packet precisionNameMetric metricTransportReal realReadPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed metricUnary transportUnary metricTransportReal
  exact
    ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, precisionUnary, metricUnary,
      realUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, precisionNameMetric, metricTransportReal, precisionPkg, realReadPkg⟩

theorem CompactUniformContinuityPacket_finite_net_handoff [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow handoff targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision net handoff ->
        Cont handoff target targetRead ->
          PkgSig bundle targetRead pkg ->
            UnaryHistory precision ∧ UnaryHistory handoff ∧ UnaryHistory targetRead ∧
              Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                Cont fold transport route ∧ Cont route nameRow precision ∧
                  Cont precision net handoff ∧ Cont handoff target targetRead ∧
                    PkgSig bundle precision pkg ∧ PkgSig bundle targetRead pkg := by
  intro packet precisionNetHandoff handoffTargetRead targetReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ := packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary netUnary precisionNetHandoff
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed handoffUnary targetUnary handoffTargetRead
  exact
    ⟨precisionUnary, handoffUnary, targetReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionNetHandoff,
      handoffTargetRead, precisionPkg, targetReadPkg⟩

theorem CompactUniformContinuityPacket_radius_fold_exactness [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        PkgSig bundle radiusRead pkg ->
          UnaryHistory precision ∧ UnaryHistory radiusRows ∧ UnaryHistory fold ∧
            UnaryHistory radiusRead ∧ Cont net coverage modulusRows ∧
              Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                Cont radiusRows fold radiusRead ∧ PkgSig bundle precision pkg ∧
                  PkgSig bundle radiusRead pkg := by
  intro packet radiusRowsFoldRadiusRead radiusReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  exact
    ⟨precisionUnary, radiusRowsUnary, foldUnary, radiusReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, radiusRowsFoldRadiusRead, precisionPkg,
      radiusReadPkg⟩

theorem CompactUniformContinuityPacket_probe_bundle_coverage [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        PkgSig bundle sourceRead pkg ->
          UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory sourceRead ∧
            Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
              Cont fold transport route ∧ Cont route nameRow precision ∧
                Cont source net sourceRead ∧ PkgSig bundle precision pkg ∧
                  PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead sourceReadPkg
  obtain ⟨sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  exact
    ⟨netUnary, coverageUnary, sourceReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, sourceNetRead,
      precisionPkg, sourceReadPkg⟩

theorem CompactUniformContinuityPacket_root_compact_net_row [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
        Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
          Cont fold transport route ∧ PkgSig bundle precision pkg := by
  intro packet
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, _radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  exact
    ⟨netUnary, coverageUnary, modulusRowsUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, precisionPkg⟩

theorem CompactUniformContinuityPacket_root_uniform_modulus_row [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision tolerance uniformRead ->
        PkgSig bundle uniformRead pkg ->
          UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory uniformRead ∧
            Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
              Cont fold transport route ∧ Cont route nameRow precision ∧
                Cont precision tolerance uniformRead ∧ PkgSig bundle precision pkg ∧
                  PkgSig bundle uniformRead pkg := by
  intro packet precisionToleranceUniform uniformReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed precisionUnary toleranceUnary precisionToleranceUniform
  exact
    ⟨toleranceUnary, precisionUnary, uniformReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision,
      precisionToleranceUniform, precisionPkg, uniformReadPkg⟩

theorem CompactUniformContinuityPacket_target_metric_totality [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow precisionRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision tolerance precisionRead ->
        Cont precisionRead target targetRead ->
          PkgSig bundle targetRead pkg ->
            UnaryHistory target ∧ UnaryHistory tolerance ∧ UnaryHistory precision ∧
              UnaryHistory precisionRead ∧ UnaryHistory targetRead ∧
                Cont route nameRow precision ∧ Cont precision tolerance precisionRead ∧
                  Cont precisionRead target targetRead ∧ PkgSig bundle precision pkg ∧
                    PkgSig bundle targetRead pkg := by
  intro packet precisionToleranceRead precisionReadTarget targetReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary toleranceUnary precisionToleranceRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionReadUnary targetUnary precisionReadTarget
  exact
    ⟨targetUnary, toleranceUnary, precisionUnary, precisionReadUnary, targetReadUnary,
      routeNamePrecision, precisionToleranceRead, precisionReadTarget, precisionPkg,
      targetReadPkg⟩

theorem CompactUniformContinuityPacket_source_metric_totality [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net metricRead ->
        Cont metricRead transport handoff ->
          PkgSig bundle metricRead pkg ->
            PkgSig bundle handoff pkg ->
              UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory metricRead ∧
                UnaryHistory handoff ∧ Cont net coverage modulusRows ∧
                  Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                    Cont source net metricRead ∧ Cont metricRead transport handoff ∧
                      PkgSig bundle precision pkg ∧ PkgSig bundle metricRead pkg ∧
                        PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro packet sourceNetMetric metricTransportHandoff metricReadPkg handoffPkg
  obtain ⟨sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, _nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed sourceUnary netUnary sourceNetMetric
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed metricReadUnary transportUnary metricTransportHandoff
  exact
    ⟨sourceUnary, netUnary, metricReadUnary, handoffUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, sourceNetMetric, metricTransportHandoff,
      precisionPkg, metricReadPkg, handoffPkg⟩

theorem CompactUniformContinuityPacket_root_metric_route [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle targetRead pkg ->
              UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                  Cont fold transport route ∧ Cont route nameRow precision ∧
                    Cont source net sourceRead ∧ Cont precision target targetRead ∧
                      PkgSig bundle precision pkg ∧ PkgSig bundle sourceRead pkg ∧
                        PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionTargetRead sourceReadPkg targetReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  exact
    ⟨sourceReadUnary,
      targetReadUnary,
      netCoverageModulusRows,
      modulusRowsRadiusRowsFold,
      foldTransportRoute,
      routeNamePrecision,
      sourceNetRead,
      precisionTargetRead,
      precisionPkg,
      sourceReadPkg,
      targetReadPkg⟩

theorem CompactUniformContinuityPacket_fold_witness_stability [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow radiusRead stablePrecision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        hsame stablePrecision radiusRead ->
          PkgSig bundle radiusRead pkg ->
            UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory radiusRead ∧
              UnaryHistory stablePrecision ∧ Cont modulusRows radiusRows fold ∧
                Cont radiusRows fold radiusRead ∧ hsame stablePrecision radiusRead ∧
                  PkgSig bundle precision pkg ∧ PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg
  intro packet radiusRowsFoldRadiusRead stablePrecisionSame radiusReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have stablePrecisionUnary : UnaryHistory stablePrecision :=
    unary_transport_symm radiusReadUnary stablePrecisionSame
  exact
    ⟨radiusRowsUnary, foldUnary, radiusReadUnary, stablePrecisionUnary,
      modulusRowsRadiusRowsFold, radiusRowsFoldRadiusRead, stablePrecisionSame, precisionPkg,
      radiusReadPkg⟩

theorem CompactUniformContinuityPacket_finite_row_audit_boundary [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead sourceRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision nameRow metricRead ->
            Cont metricRead transport realRead ->
              PkgSig bundle sourceRead pkg ->
                PkgSig bundle targetRead pkg ->
                  PkgSig bundle realRead pkg ->
                    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                      UnaryHistory tolerance ∧ UnaryHistory net ∧ UnaryHistory coverage ∧
                        UnaryHistory modulusRows ∧ UnaryHistory radiusRows ∧
                          UnaryHistory fold ∧ UnaryHistory route ∧ UnaryHistory precision ∧
                            UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                              UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                                Cont net coverage modulusRows ∧
                                  Cont modulusRows radiusRows fold ∧
                                    Cont fold transport route ∧ Cont route nameRow precision ∧
                                      Cont source net sourceRead ∧
                                        Cont precision target targetRead ∧
                                          Cont precision nameRow metricRead ∧
                                            Cont metricRead transport realRead ∧
                                              PkgSig bundle precision pkg ∧
                                                PkgSig bundle sourceRead pkg ∧
                                                  PkgSig bundle targetRead pkg ∧
                                                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    sourceReadPkg targetReadPkg realReadPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  exact
    ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
      modulusRowsUnary, radiusRowsUnary, foldUnary, routeUnary, precisionUnary,
      sourceReadUnary, targetReadUnary, metricReadUnary, realReadUnary,
      netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, sourceNetRead, precisionTargetRead, precisionNameMetric,
      metricTransportReal, precisionPkg, sourceReadPkg, targetReadPkg, realReadPkg⟩

theorem CompactUniformContinuityPacket_root_namecert_unblock_package
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead metricRead realRead radiusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont source net sourceRead →
        Cont precision target targetRead →
          Cont precision nameRow metricRead →
            Cont metricRead transport realRead →
              Cont radiusRows fold radiusRead →
                PkgSig bundle sourceRead pkg →
                  PkgSig bundle targetRead pkg →
                    PkgSig bundle realRead pkg →
                      PkgSig bundle radiusRead pkg →
                        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                          UnaryHistory tolerance ∧ UnaryHistory precision ∧
                            UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                              UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                                UnaryHistory radiusRead ∧
                                  Cont net coverage modulusRows ∧
                                    Cont modulusRows radiusRows fold ∧
                                      Cont fold transport route ∧
                                        Cont route nameRow precision ∧
                                          Cont source net sourceRead ∧
                                            Cont precision target targetRead ∧
                                              Cont precision nameRow metricRead ∧
                                                Cont metricRead transport realRead ∧
                                                  Cont radiusRows fold radiusRead ∧
                                                    PkgSig bundle precision pkg ∧
                                                      PkgSig bundle sourceRead pkg ∧
                                                        PkgSig bundle targetRead pkg ∧
                                                          PkgSig bundle realRead pkg ∧
                                                            PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    radiusRowsFoldRadiusRead sourceReadPkg targetReadPkg realReadPkg radiusReadPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
    radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  exact
    ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, precisionUnary, sourceReadUnary,
      targetReadUnary, metricReadUnary, realReadUnary, radiusReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, sourceNetRead,
      precisionTargetRead, precisionNameMetric, metricTransportReal, radiusRowsFoldRadiusRead,
      precisionPkg, sourceReadPkg, targetReadPkg, realReadPkg, radiusReadPkg⟩

theorem CompactUniformContinuityPacket_root_rational_fold_route [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow radiusRead precisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        hsame precisionRead precision ->
          PkgSig bundle radiusRead pkg ->
            UnaryHistory precision ∧ UnaryHistory radiusRows ∧ UnaryHistory fold ∧
              UnaryHistory radiusRead ∧ UnaryHistory precisionRead ∧
                Cont modulusRows radiusRows fold ∧ Cont radiusRows fold radiusRead ∧
                  hsame precisionRead precision ∧ PkgSig bundle precision pkg ∧
                    PkgSig bundle radiusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet radiusRowsFoldRadiusRead precisionReadSame radiusReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
    modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_transport_symm precisionUnary precisionReadSame
  exact
    ⟨precisionUnary, radiusRowsUnary, foldUnary, radiusReadUnary, precisionReadUnary,
      modulusRowsRadiusRowsFold, radiusRowsFoldRadiusRead, precisionReadSame, precisionPkg,
      radiusReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
