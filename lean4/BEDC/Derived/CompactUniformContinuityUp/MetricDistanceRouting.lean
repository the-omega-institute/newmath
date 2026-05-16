import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_metric_distance_routing [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow sourceRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont source coverage sourceRead ->
        Cont target modulusRows targetRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle targetRead pkg ->
              UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧ UnaryHistory source ∧
                UnaryHistory target ∧ Cont source coverage sourceRead ∧
                  Cont target modulusRows targetRead ∧ PkgSig bundle sourceRead pkg ∧
                    PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet sourceCoverageRead targetModulusRead sourceReadPkg targetReadPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
    _radiusRowsUnary, _transportUnary, _nameRowUnary, netCoverageModulusRows,
    _modulusRowsRadiusRowsFold, _foldTransportRoute, _routeNamePrecision, _precisionPkg⟩ :=
      packet
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary coverageUnary sourceCoverageRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary modulusRowsUnary targetModulusRead
  exact
    ⟨sourceReadUnary, targetReadUnary, sourceUnary, targetUnary, sourceCoverageRead,
      targetModulusRead, sourceReadPkg, targetReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
