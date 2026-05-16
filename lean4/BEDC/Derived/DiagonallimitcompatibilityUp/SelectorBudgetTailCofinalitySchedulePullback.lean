import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_tail_cofinality_schedule_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      precision scheduleWindow scheduleDyadic scheduleRegseq scheduleSeal scheduleTransport
      scheduleRoute scheduleProvenance scheduleLocalCert scheduleEndpoint selector tailRead
      sharedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      BEDC.Derived.TailCofinalityScheduleUp.TailCofinalityScheduleCarrier precision
        scheduleWindow scheduleDyadic scheduleRegseq scheduleSeal scheduleTransport scheduleRoute
        scheduleProvenance scheduleLocalCert scheduleEndpoint bundle pkg ->
      Cont diagonal windows selector ->
      Cont selector scheduleEndpoint tailRead ->
      Cont tailRead realSeal sharedRoute ->
      PkgSig bundle tailRead pkg ->
      PkgSig bundle sharedRoute pkg ->
      UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory selector ∧
        UnaryHistory scheduleEndpoint ∧ UnaryHistory tailRead ∧ UnaryHistory realSeal ∧
          UnaryHistory sharedRoute ∧ Cont diagonal windows selector ∧
            Cont selector scheduleEndpoint tailRead ∧ Cont tailRead realSeal sharedRoute ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle scheduleEndpoint pkg ∧
                PkgSig bundle tailRead pkg ∧ PkgSig bundle sharedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro diagonalCarrier scheduleCarrier diagonalWindowsSelector selectorScheduleTail
    tailRealShared tailReadPkg sharedRoutePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨_precisionUnary, _scheduleWindowUnary, _scheduleDyadicUnary, _scheduleRegseqUnary,
    _scheduleSealUnary, _scheduleTransportUnary, _scheduleRouteUnary,
    _scheduleProvenanceUnary, _scheduleLocalCertUnary, scheduleEndpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute,
    _routeProvenanceEndpoint, _endpointLocalCert, scheduleEndpointPkg⟩ := scheduleCarrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed selectorUnary scheduleEndpointUnary selectorScheduleTail
  have sharedRouteUnary : UnaryHistory sharedRoute :=
    unary_cont_closed tailReadUnary realSealUnary tailRealShared
  exact
    ⟨diagonalUnary, windowsUnary, selectorUnary, scheduleEndpointUnary, tailReadUnary,
      realSealUnary, sharedRouteUnary, diagonalWindowsSelector, selectorScheduleTail,
      tailRealShared, provenancePkg, scheduleEndpointPkg, tailReadPkg, sharedRoutePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
