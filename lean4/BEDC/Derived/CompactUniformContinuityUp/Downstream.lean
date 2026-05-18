import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_root_downstream_unblock_package [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead metricRead realRead radiusRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision nameRow metricRead ->
            Cont metricRead transport realRead ->
              Cont radiusRows fold radiusRead ->
                Cont precision tolerance uniformRead ->
                  PkgSig bundle sourceRead pkg ->
                    PkgSig bundle targetRead pkg ->
                      PkgSig bundle realRead pkg ->
                        PkgSig bundle radiusRead pkg ->
                          PkgSig bundle uniformRead pkg ->
                            UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                              UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                                UnaryHistory radiusRead ∧ UnaryHistory uniformRead ∧
                                  Cont net coverage modulusRows ∧
                                    Cont modulusRows radiusRows fold ∧
                                      Cont fold transport route ∧
                                        Cont route nameRow precision ∧
                                          Cont source net sourceRead ∧
                                            Cont precision target targetRead ∧
                                              Cont precision nameRow metricRead ∧
                                                Cont metricRead transport realRead ∧
                                                  Cont radiusRows fold radiusRead ∧
                                                    Cont precision tolerance uniformRead ∧
                                                      PkgSig bundle precision pkg ∧
                                                        PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    radiusRowsFoldRadiusRead precisionToleranceUniform _sourceReadPkg _targetReadPkg
    _realReadPkg _radiusReadPkg uniformReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, toleranceUnary, netUnary, coverageUnary,
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
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed precisionUnary toleranceUnary precisionToleranceUniform
  exact
    ⟨sourceReadUnary, targetReadUnary, metricReadUnary, realReadUnary, radiusReadUnary,
      uniformReadUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, sourceNetRead, precisionTargetRead, precisionNameMetric,
      metricTransportReal, radiusRowsFoldRadiusRead, precisionToleranceUniform, precisionPkg,
      uniformReadPkg⟩

theorem CompactUniformContinuityPacket_rational_fold_export [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow radiusRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont radiusRows fold radiusRead ->
        Cont precision transport downstreamRead ->
          PkgSig bundle radiusRead pkg ->
            PkgSig bundle downstreamRead pkg ->
              UnaryHistory precision ∧ UnaryHistory radiusRead ∧ UnaryHistory downstreamRead ∧
                Cont modulusRows radiusRows fold ∧ Cont radiusRows fold radiusRead ∧
                  Cont precision transport downstreamRead ∧ PkgSig bundle precision pkg ∧
                    PkgSig bundle radiusRead pkg ∧ PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet radiusRowsFoldRadiusRead precisionTransportDownstream radiusReadPkg downstreamReadPkg
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
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed precisionUnary transportUnary precisionTransportDownstream
  exact
    ⟨precisionUnary, radiusReadUnary, downstreamReadUnary, modulusRowsRadiusRowsFold,
      radiusRowsFoldRadiusRead, precisionTransportDownstream, precisionPkg, radiusReadPkg,
      downstreamReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
