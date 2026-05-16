import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_complete_metric_consumer_route
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont u v t →
        Cont t w selected →
          Cont selected q readback →
            Cont readback e sealRead →
              Cont sealRead h terminal →
                PkgSig bundle terminal pkg →
                  UnaryHistory selected ∧ UnaryHistory readback ∧
                    UnaryHistory sealRead ∧ UnaryHistory terminal ∧ Cont u v t ∧
                      Cont t w selected ∧ Cont selected q readback ∧
                        Cont readback e sealRead ∧ Cont sealRead h terminal ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier uvt selectedRoute readbackRoute sealRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
      hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _carrierUvt, _twq, _qeh,
      pPkg, _hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealUnary hUnary terminalRoute
  exact
    ⟨selectedUnary, readbackUnary, sealUnary, terminalUnary, uvt, selectedRoute,
      readbackRoute, sealRoute, terminalRoute, pPkg, terminalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
