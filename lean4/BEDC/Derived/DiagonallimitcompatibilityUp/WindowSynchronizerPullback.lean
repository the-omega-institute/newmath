import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityWindowSynchronizerPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      syncWindow syncReadback syncSeal syncRealSeal syncBudget syncRoute syncEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      hsame windows syncWindow ->
        hsame readback syncReadback ->
          hsame sealRow syncSeal ->
            hsame realSeal syncRealSeal ->
              hsame dyadic syncBudget ->
                Cont syncBudget syncWindow syncRoute ->
                  Cont syncRoute syncReadback syncEndpoint ->
                    PkgSig bundle syncEndpoint pkg ->
                      UnaryHistory syncWindow ∧ UnaryHistory syncReadback ∧
                        UnaryHistory syncRoute ∧ UnaryHistory syncEndpoint ∧
                          hsame windows syncWindow ∧ hsame readback syncReadback ∧
                            Cont syncBudget syncWindow syncRoute ∧
                              Cont syncRoute syncReadback syncEndpoint ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle syncEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sameWindow sameReadback _sameSeal _sameRealSeal sameBudget
    budgetWindowSync syncReadbackEndpoint endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have syncBudgetUnary : UnaryHistory syncBudget :=
    unary_transport dyadicUnary sameBudget
  have syncWindowUnary : UnaryHistory syncWindow :=
    unary_transport windowsUnary sameWindow
  have syncReadbackUnary : UnaryHistory syncReadback :=
    unary_transport readbackUnary sameReadback
  have syncRouteUnary : UnaryHistory syncRoute :=
    unary_cont_closed syncBudgetUnary syncWindowUnary budgetWindowSync
  have syncEndpointUnary : UnaryHistory syncEndpoint :=
    unary_cont_closed syncRouteUnary syncReadbackUnary syncReadbackEndpoint
  exact
    ⟨syncWindowUnary, syncReadbackUnary, syncRouteUnary, syncEndpointUnary, sameWindow,
      sameReadback, budgetWindowSync, syncReadbackEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
