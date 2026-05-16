import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_route_determinacy [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          Cont readback e sealRow →
            Cont sealRow h endpoint →
              PkgSig bundle endpoint pkg →
                UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                  UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                    UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
                      UnaryHistory endpoint ∧ Cont m0 m1 u ∧ Cont u v t ∧
                        Cont t w selected ∧ Cont selected q readback ∧
                          Cont readback e sealRow ∧ Cont sealRow h endpoint ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg ∧
                              hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier selectedRoute readbackRoute sealRoute endpointRoute endpointPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary hUnary endpointRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, selectedUnary,
      readbackUnary, sealUnary, endpointUnary, m0m1u, uvt, selectedRoute, readbackRoute,
      sealRoute, endpointRoute, pPkg, endpointPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
