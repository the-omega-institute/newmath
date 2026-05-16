import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_uniform_precision_consumer_route [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport route
      nameRow sourceRead metricRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage modulusRows
        radiusRows fold transport route nameRow bundle pkg →
      Cont source net sourceRead →
        Cont precision nameRow metricRead →
          Cont metricRead transport targetRead →
            PkgSig bundle sourceRead pkg →
              PkgSig bundle targetRead pkg →
                UnaryHistory source ∧ UnaryHistory net ∧ UnaryHistory precision ∧
                  UnaryHistory sourceRead ∧ UnaryHistory metricRead ∧ UnaryHistory targetRead ∧
                    Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                      Cont fold transport route ∧ Cont route nameRow precision ∧
                        Cont source net sourceRead ∧ Cont precision nameRow metricRead ∧
                          Cont metricRead transport targetRead ∧ PkgSig bundle precision pkg ∧
                            PkgSig bundle sourceRead pkg ∧ PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetRead precisionNameMetric metricTransportTarget sourceReadPkg
    targetReadPkg
  obtain ⟨sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
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
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary netUnary sourceNetRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportTarget
  exact
    ⟨sourceUnary, netUnary, precisionUnary, sourceReadUnary, metricReadUnary,
      targetReadUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, sourceNetRead, precisionNameMetric, metricTransportTarget,
      precisionPkg, sourceReadPkg, targetReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
