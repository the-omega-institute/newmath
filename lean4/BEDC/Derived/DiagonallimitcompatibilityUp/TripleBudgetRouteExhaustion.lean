import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_triple_budget_route_exhaustion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tail schedule observation publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tail ->
          UnaryHistory observation ->
            Cont sealRow request sealBudget ->
              Cont sealBudget tail schedule ->
                Cont schedule observation publicRead ->
                  PkgSig bundle publicRead pkg ->
                    UnaryHistory sealRow ∧ UnaryHistory request ∧ UnaryHistory sealBudget ∧
                      UnaryHistory tail ∧ UnaryHistory schedule ∧ UnaryHistory observation ∧
                        UnaryHistory publicRead ∧ Cont sealRow request sealBudget ∧
                          Cont sealBudget tail schedule ∧ Cont schedule observation publicRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier requestUnary tailUnary observationUnary sealRowRequestSealBudget
    sealBudgetTailSchedule scheduleObservationPublicRead publicReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed sealRowUnary requestUnary sealRowRequestSealBudget
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSchedule
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationPublicRead
  exact
    ⟨sealRowUnary, requestUnary, sealBudgetUnary, tailUnary, scheduleUnary,
      observationUnary, publicReadUnary, sealRowRequestSealBudget, sealBudgetTailSchedule,
      scheduleObservationPublicRead, provenancePkg, publicReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
