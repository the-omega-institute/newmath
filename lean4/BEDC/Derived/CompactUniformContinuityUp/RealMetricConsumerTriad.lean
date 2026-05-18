import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_real_metric_consumer_triad [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead triadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision nameRow metricRead ->
        Cont metricRead transport realRead ->
          Cont net metricRead triadRead ->
            PkgSig bundle realRead pkg ->
              PkgSig bundle triadRead pkg ->
                UnaryHistory net ∧ UnaryHistory metricRead ∧ UnaryHistory realRead ∧
                  UnaryHistory triadRead ∧ Cont net coverage modulusRows ∧
                    Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                      Cont precision nameRow metricRead ∧
                        Cont metricRead transport realRead ∧
                          Cont net metricRead triadRead ∧ PkgSig bundle precision pkg ∧
                            PkgSig bundle realRead pkg ∧ PkgSig bundle triadRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet precisionNameMetric metricTransportReal netMetricTriad realReadPkg triadReadPkg
  obtain
    ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have triadReadUnary : UnaryHistory triadRead :=
    unary_cont_closed netUnary metricReadUnary netMetricTriad
  exact
    ⟨netUnary, metricReadUnary, realReadUnary, triadReadUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, precisionNameMetric,
      metricTransportReal, netMetricTriad, precisionPkg, realReadPkg, triadReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
