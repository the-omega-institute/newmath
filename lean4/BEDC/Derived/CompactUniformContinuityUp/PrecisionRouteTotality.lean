import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_precision_route_totality [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead metricRead realRead radiusRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision nameRow metricRead ->
            Cont metricRead transport realRead ->
              Cont radiusRows fold radiusRead ->
                Cont precision net handoff ->
                  PkgSig bundle sourceRead pkg ->
                    PkgSig bundle targetRead pkg ->
                      PkgSig bundle realRead pkg ->
                        PkgSig bundle radiusRead pkg ->
                          PkgSig bundle handoff pkg ->
                            UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                              UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                                UnaryHistory radiusRead ∧ UnaryHistory handoff ∧
                                  Cont net coverage modulusRows ∧
                                    Cont modulusRows radiusRows fold ∧
                                      Cont fold transport route ∧
                                        Cont route nameRow precision ∧
                                          Cont precision net handoff ∧
                                            PkgSig bundle precision pkg ∧
                                              PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    radiusRowsFoldRadiusRead precisionNetHandoff _sourceReadPkg _targetReadPkg _realReadPkg
    _radiusReadPkg handoffPkg
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
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusRowsFoldRadiusRead
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed precisionUnary netUnary precisionNetHandoff
  exact
    ⟨sourceReadUnary, targetReadUnary, metricReadUnary, realReadUnary, radiusReadUnary,
      handoffUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, precisionNetHandoff, precisionPkg, handoffPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
