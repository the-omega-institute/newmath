import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_finite_net_factorization [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg ->
      UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
        UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory route ∧
          UnaryHistory precision ∧ Cont net coverage modulusRows ∧
            Cont modulusRows radiusRows fold ∧ Cont fold transport route ∧
              Cont route nameRow precision ∧ PkgSig bundle precision pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet
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
  exact
    ⟨netUnary, coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, routeUnary,
      precisionUnary, netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      routeNamePrecision, precisionPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
