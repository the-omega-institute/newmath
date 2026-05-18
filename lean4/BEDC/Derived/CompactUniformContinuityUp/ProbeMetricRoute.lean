import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_probe_metric_route [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow probeRead metricRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net probeRead ->
        Cont probeRead target metricRead ->
          Cont metricRead modulusRows modulusRead ->
            PkgSig bundle modulusRead pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
                  UnaryHistory probeRead ∧ UnaryHistory metricRead ∧
                    UnaryHistory modulusRead ∧ Cont net coverage modulusRows ∧
                      Cont source net probeRead ∧ Cont probeRead target metricRead ∧
                        Cont metricRead modulusRows modulusRead ∧
                          PkgSig bundle precision pkg ∧ PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceNetProbe probeTargetMetric metricModulusRead modulusPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _toleranceUnary, netUnary, coverageUnary,
    _radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    _modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have probeReadUnary : UnaryHistory probeRead :=
    unary_cont_closed sourceUnary netUnary sourceNetProbe
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed probeReadUnary targetUnary probeTargetMetric
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed metricReadUnary modulusRowsUnary metricModulusRead
  exact
    ⟨sourceUnary, targetUnary, graphUnary, netUnary, coverageUnary, modulusRowsUnary,
      probeReadUnary, metricReadUnary, modulusReadUnary, netCoverageModulusRows,
        sourceNetProbe, probeTargetMetric, metricModulusRead, precisionPkg, modulusPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
