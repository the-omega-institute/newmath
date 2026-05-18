import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_bridge_non_escape_boundary [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision route bridgeRead ->
        PkgSig bundle bridgeRead pkg ->
          UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
            UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory bridgeRead ∧
              Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                Cont fold transport route ∧ Cont precision route bridgeRead ∧
                  PkgSig bundle precision pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg AskSetup PackageSetup
  intro packet precisionRouteBridge bridgePkg
  rcases packet with
    ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
      coverageUnary, radiusRowsUnary, transportUnary, nameRowUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision, precisionPkg⟩
  have modulusRowsUnary : UnaryHistory modulusRows :=
    unary_cont_closed netUnary coverageUnary netCoverageModulusRows
  have foldUnary : UnaryHistory fold :=
    unary_cont_closed modulusRowsUnary radiusRowsUnary modulusRowsRadiusRowsFold
  have routeUnary : UnaryHistory route :=
    unary_cont_closed foldUnary transportUnary foldTransportRoute
  have precisionUnary : UnaryHistory precision :=
    unary_cont_closed routeUnary nameRowUnary routeNamePrecision
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteBridge
  exact
    ⟨netUnary, coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, bridgeUnary,
      netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      precisionRouteBridge, precisionPkg, bridgePkg⟩

end BEDC.Derived.CompactUniformContinuityUp
