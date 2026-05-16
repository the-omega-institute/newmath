import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_center_radius_compatibility [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow centerRead halfRadiusRead sourceMetricRead targetMetricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage centerRead ->
        Cont centerRead radiusRows halfRadiusRead ->
          Cont source centerRead sourceMetricRead ->
            Cont graph target targetMetricRead ->
              PkgSig bundle halfRadiusRead pkg ->
                PkgSig bundle sourceMetricRead pkg ->
                  PkgSig bundle targetMetricRead pkg ->
                    UnaryHistory centerRead /\ UnaryHistory halfRadiusRead /\
                      UnaryHistory sourceMetricRead /\ UnaryHistory targetMetricRead /\
                        Cont net coverage centerRead /\
                          Cont centerRead radiusRows halfRadiusRead /\
                            Cont source centerRead sourceMetricRead /\
                              Cont graph target targetMetricRead /\
                                PkgSig bundle halfRadiusRead pkg /\
                                  PkgSig bundle sourceMetricRead pkg /\
                                    PkgSig bundle targetMetricRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet netCoverageCenter centerRadiusHalf sourceCenterMetric graphTargetMetric
    halfRadiusPkg sourceMetricPkg targetMetricPkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _toleranceUnary, netUnary,
    coverageUnary, radiusRowsUnary, _transportUnary, _nameRowUnary, _netCoverageModulusRows,
    _modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, _precisionPkg⟩ :=
      packet
  have centerUnary : UnaryHistory centerRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCenter
  have halfRadiusUnary : UnaryHistory halfRadiusRead :=
    unary_cont_closed centerUnary radiusRowsUnary centerRadiusHalf
  have sourceMetricUnary : UnaryHistory sourceMetricRead :=
    unary_cont_closed sourceUnary centerUnary sourceCenterMetric
  have targetMetricUnary : UnaryHistory targetMetricRead :=
    unary_cont_closed graphUnary targetUnary graphTargetMetric
  exact
    ⟨centerUnary, halfRadiusUnary, sourceMetricUnary, targetMetricUnary, netCoverageCenter,
      centerRadiusHalf, sourceCenterMetric, graphTargetMetric, halfRadiusPkg, sourceMetricPkg,
      targetMetricPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
