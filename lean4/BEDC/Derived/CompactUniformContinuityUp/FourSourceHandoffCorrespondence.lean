import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_four_source_handoff_correspondence
    [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow compactRead continuousRead metricRead rationalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont net coverage compactRead ->
        Cont compactRead graph continuousRead ->
          Cont continuousRead target metricRead ->
            Cont radiusRows fold rationalRead ->
              Cont rationalRead metricRead realRead ->
                PkgSig bundle realRead pkg ->
                  UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                    UnaryHistory metricRead ∧ UnaryHistory rationalRead ∧
                      UnaryHistory realRead ∧ Cont net coverage compactRead ∧
                        Cont compactRead graph continuousRead ∧
                          Cont continuousRead target metricRead ∧
                            Cont radiusRows fold rationalRead ∧
                              Cont rationalRead metricRead realRead ∧
                                PkgSig bundle precision pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet netCoverageCompact compactGraphContinuous continuousTargetMetric
    radiusFoldRational rationalMetricReal realPkg
  obtain
    ⟨_sourceUnary, targetUnary, graphUnary, _toleranceUnary, netUnary, coverageUnary,
      radiusRowsUnary, transportUnary, _nameRowUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, _routeNamePrecision, precisionPkg⟩ :=
      packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed netUnary coverageUnary netCoverageCompact
  have continuousReadUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactReadUnary graphUnary compactGraphContinuous
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed continuousReadUnary targetUnary continuousTargetMetric
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have _routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed radiusRowsUnary foldUnary radiusFoldRational
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rationalReadUnary metricReadUnary rationalMetricReal
  exact
    ⟨compactReadUnary, continuousReadUnary, metricReadUnary, rationalReadUnary,
      realReadUnary, netCoverageCompact, compactGraphContinuous, continuousTargetMetric,
      radiusFoldRational, rationalMetricReal, precisionPkg, realPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
