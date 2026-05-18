import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_root_probebundle_center_selection
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source coverage centerRead ->
        Cont centerRead transport metricRead ->
          PkgSig bundle centerRead pkg ->
            PkgSig bundle metricRead pkg ->
              UnaryHistory source ∧ UnaryHistory coverage ∧ UnaryHistory centerRead ∧
                UnaryHistory metricRead ∧ Cont net coverage modulusRows ∧
                  Cont source coverage centerRead ∧ Cont centerRead transport metricRead ∧
                    PkgSig bundle centerRead pkg ∧ PkgSig bundle metricRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceCoverageCenter centerTransportMetric centerReadPkg metricReadPkg
  obtain ⟨sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    _radiusRowsUnary, transportUnary, _nameRowUnary, netCoverageModulusRows,
    _modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, _precisionPkg⟩ :=
      packet
  have centerReadUnary : UnaryHistory centerRead :=
    unary_cont_closed sourceUnary coverageUnary sourceCoverageCenter
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed centerReadUnary transportUnary centerTransportMetric
  exact
    ⟨sourceUnary, coverageUnary, centerReadUnary, metricReadUnary, netCoverageModulusRows,
      sourceCoverageCenter, centerTransportMetric, centerReadPkg, metricReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
