import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_constant_map_consumer_route [AskSetup] [PackageSetup]
    {source graph tolerance precision net coverage modulusRows radiusRows fold transport route
      nameRow constantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source BHist.Empty graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision BHist.Empty constantRead ->
        PkgSig bundle constantRead pkg ->
          UnaryHistory source ∧ UnaryHistory BHist.Empty ∧ UnaryHistory precision ∧
            UnaryHistory constantRead ∧ Cont net coverage modulusRows ∧
              Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
                Cont route nameRow precision ∧ Cont precision BHist.Empty constantRead ∧
                  PkgSig bundle precision pkg ∧ PkgSig bundle constantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet precisionEmptyConstant constantPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
  have constantUnary : UnaryHistory constantRead :=
    unary_cont_closed precisionUnary targetUnary precisionEmptyConstant
  exact
    ⟨sourceUnary, targetUnary, precisionUnary, constantUnary, netCoverageModulusRows,
      modulusRowsRadiusRowsFold, foldTransportRoute, routeNamePrecision,
      precisionEmptyConstant, precisionPkg, constantPkg⟩

theorem CompactUniformContinuityPacket_real_interval_consumer_route [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow leftEndpoint rightEndpoint intervalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage modulusRows
        radiusRows fold transport route nameRow bundle pkg ->
      Cont precision target leftEndpoint ->
        Cont leftEndpoint transport rightEndpoint ->
          Cont rightEndpoint nameRow intervalRead ->
            PkgSig bundle intervalRead pkg ->
              UnaryHistory precision ∧ UnaryHistory target ∧ UnaryHistory leftEndpoint ∧
                UnaryHistory rightEndpoint ∧ UnaryHistory intervalRead ∧
                  Cont route nameRow precision ∧ Cont precision target leftEndpoint ∧
                    Cont leftEndpoint transport rightEndpoint ∧
                      Cont rightEndpoint nameRow intervalRead ∧ PkgSig bundle precision pkg ∧
                        PkgSig bundle intervalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet precisionTargetLeft leftTransportRight rightNameInterval intervalPkg
  obtain ⟨_sourceUnary, targetUnary, _graphUnary, _toleranceUnary, netUnary, coverageUnary,
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
  have leftUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed precisionUnary targetUnary precisionTargetLeft
  have rightUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed leftUnary transportUnary leftTransportRight
  have intervalUnary : UnaryHistory intervalRead :=
    unary_cont_closed rightUnary nameRowUnary rightNameInterval
  exact
    ⟨precisionUnary, targetUnary, leftUnary, rightUnary, intervalUnary, routeNamePrecision,
      precisionTargetLeft, leftTransportRight, rightNameInterval, precisionPkg, intervalPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
