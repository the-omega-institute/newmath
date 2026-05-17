import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_terminal_budget_factorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetSource windowLock regularRead sealRoute terminal publicRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic budgetSource ->
        Cont budgetSource windows windowLock ->
          Cont windowLock readback regularRead ->
            Cont regularRead sealRow sealRoute ->
              Cont sealRoute realSeal terminal ->
                Cont terminal cert publicRead ->
                  Cont publicRead route auditRead ->
                    PkgSig bundle terminal pkg ->
                      PkgSig bundle publicRead pkg ->
                        PkgSig bundle auditRead pkg ->
                          UnaryHistory budgetSource ∧ UnaryHistory windowLock ∧
                            UnaryHistory regularRead ∧ UnaryHistory sealRoute ∧
                              UnaryHistory terminal ∧ UnaryHistory publicRead ∧
                                UnaryHistory auditRead ∧ Cont diagonal dyadic budgetSource ∧
                                  Cont budgetSource windows windowLock ∧
                                    Cont windowLock readback regularRead ∧
                                      Cont regularRead sealRow sealRoute ∧
                                        Cont sealRoute realSeal terminal ∧
                                          Cont terminal cert publicRead ∧
                                            Cont publicRead route auditRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle terminal pkg ∧
                                                  PkgSig bundle publicRead pkg ∧
                                                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalDyadicBudgetSource budgetSourceWindowsLock
    windowLockReadbackRegular regularReadSealRoute sealRouteRealSealTerminal
    terminalCertPublicRead publicReadRouteAuditRead terminalPkg publicReadPkg auditReadPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetSourceUnary : UnaryHistory budgetSource :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicBudgetSource
  have windowLockUnary : UnaryHistory windowLock :=
    unary_cont_closed budgetSourceUnary windowsUnary budgetSourceWindowsLock
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowLockUnary readbackUnary windowLockReadbackRegular
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regularReadUnary sealRowUnary regularReadSealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealRouteUnary realSealUnary sealRouteRealSealTerminal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed terminalUnary certUnary terminalCertPublicRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed publicReadUnary routeUnary publicReadRouteAuditRead
  exact
    ⟨budgetSourceUnary, windowLockUnary, regularReadUnary, sealRouteUnary, terminalUnary,
      publicReadUnary, auditReadUnary, diagonalDyadicBudgetSource, budgetSourceWindowsLock,
      windowLockReadbackRegular, regularReadSealRoute, sealRouteRealSealTerminal,
      terminalCertPublicRead, publicReadRouteAuditRead, provenancePkg, terminalPkg,
      publicReadPkg, auditReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
