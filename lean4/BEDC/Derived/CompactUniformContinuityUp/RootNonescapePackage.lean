import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_root_nonescape_package [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      Cont precision nameRow realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory precision ∧ UnaryHistory net ∧ UnaryHistory coverage ∧
            UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory realRead ∧
              Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                Cont fold transport route ∧ Cont route nameRow precision ∧
                  Cont precision nameRow realRead ∧ PkgSig bundle precision pkg ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet precisionNameReal realReadPkg
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _toleranceUnary, netUnary,
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
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed precisionUnary nameRowUnary precisionNameReal
  exact
    ⟨precisionUnary, netUnary, coverageUnary, radiusRowsUnary, foldUnary, realReadUnary,
      netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, precisionNameReal, precisionPkg, realReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
