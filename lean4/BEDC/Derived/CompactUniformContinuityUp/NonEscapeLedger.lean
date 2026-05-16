import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_non_escape_ledger [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      Cont precision route auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory net ∧ UnaryHistory coverage ∧ UnaryHistory modulusRows ∧
            UnaryHistory radiusRows ∧ UnaryHistory fold ∧ UnaryHistory auditRead ∧
              Cont net coverage modulusRows ∧ Cont modulusRows radiusRows fold ∧
                Cont fold transport route ∧ Cont precision route auditRead ∧
                  PkgSig bundle precision pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro packet precisionRouteAudit auditReadPkg
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
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteAudit
  exact
    ⟨netUnary, coverageUnary, modulusRowsUnary, radiusRowsUnary, foldUnary, auditReadUnary,
      netCoverageModulusRows, modulusRowsRadiusRowsFold, foldTransportRoute,
      precisionRouteAudit, precisionPkg, auditReadPkg⟩

end BEDC.Derived.CompactUniformContinuityUp
