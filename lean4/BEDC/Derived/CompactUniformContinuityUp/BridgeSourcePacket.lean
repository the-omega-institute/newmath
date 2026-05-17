import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_bridge_source_packet [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow bridgeSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont source target bridgeSource →
        PkgSig bundle bridgeSource pkg →
          UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
            UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory net ∧
              UnaryHistory coverage ∧ UnaryHistory modulusRows ∧ UnaryHistory radiusRows ∧
                UnaryHistory fold ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                  UnaryHistory nameRow ∧ UnaryHistory bridgeSource ∧
                    Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                      Cont fold transport route ∧ Cont route nameRow precision ∧
                        Cont source target bridgeSource ∧ PkgSig bundle precision pkg ∧
                          PkgSig bundle bridgeSource pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro packet sourceTargetBridgeSource bridgeSourcePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, netUnary, coverageUnary,
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
  have bridgeSourceUnary : UnaryHistory bridgeSource :=
    unary_cont_closed sourceUnary targetUnary sourceTargetBridgeSource
  exact
    ⟨sourceUnary, targetUnary, graphUnary, toleranceUnary, precisionUnary, netUnary,
      coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, transportUnary, routeUnary,
      nameRowUnary, bridgeSourceUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold,
      foldTransportRoute, routeNamePrecision, sourceTargetBridgeSource, precisionPkg,
      bridgeSourcePkg⟩

end BEDC.Derived.CompactUniformContinuityUp
