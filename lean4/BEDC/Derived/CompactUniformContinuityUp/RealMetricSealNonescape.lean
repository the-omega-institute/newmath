import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_real_metric_seal_nonescape [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow metricRead realRead sourceRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source net sourceRead ->
        Cont precision target targetRead ->
          Cont precision nameRow metricRead ->
            Cont metricRead transport realRead ->
              hsame realRead targetRead ->
                PkgSig bundle sourceRead pkg ->
                  PkgSig bundle targetRead pkg ->
                    PkgSig bundle realRead pkg ->
                      UnaryHistory realRead ∧ UnaryHistory targetRead ∧
                        hsame realRead targetRead ∧ Cont source net sourceRead ∧
                          Cont precision target targetRead ∧
                            Cont precision nameRow metricRead ∧
                              Cont metricRead transport realRead ∧
                                PkgSig bundle precision pkg ∧
                                  PkgSig bundle realRead pkg ∧
                                    PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro packet sourceNetRead precisionTargetRead precisionNameMetric metricTransportReal
    realSameTarget _sourceReadPkg targetReadPkg realReadPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary,
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
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameMetric
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed metricReadUnary transportUnary metricTransportReal
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed precisionUnary targetUnary precisionTargetRead
  exact
    ⟨realReadUnary, targetReadUnary, realSameTarget, sourceNetRead, precisionTargetRead,
      precisionNameMetric, metricTransportReal, precisionPkg, realReadPkg, targetReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
