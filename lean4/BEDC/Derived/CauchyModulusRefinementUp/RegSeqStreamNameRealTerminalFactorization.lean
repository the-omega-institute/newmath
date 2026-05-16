import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_regseq_streamname_real_terminal_factorization
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectorRead windowRead toleranceRead sealRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont v t selectorRead ->
        Cont selectorRead w windowRead ->
          Cont windowRead q toleranceRead ->
            Cont toleranceRead e sealRead ->
              Cont sealRead h terminalRead ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory selectorRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory terminalRead ∧ Cont v t selectorRead ∧
                        Cont selectorRead w windowRead ∧ Cont windowRead q toleranceRead ∧
                          Cont toleranceRead e sealRead ∧ Cont sealRead h terminalRead ∧
                            PkgSig bundle terminalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier selectorRoute windowRoute toleranceRoute sealRoute terminalRoute terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
      hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, hn⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed vUnary tUnary selectorRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed selectorUnary wUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealUnary hUnary terminalRoute
  exact
    ⟨selectorUnary, windowUnary, toleranceUnary, sealUnary, terminalUnary, selectorRoute,
      windowRoute, toleranceRoute, sealRoute, terminalRoute, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
