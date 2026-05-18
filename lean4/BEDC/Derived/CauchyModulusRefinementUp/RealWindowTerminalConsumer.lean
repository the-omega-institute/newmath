import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRealWindowTerminalConsumer [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n budgetRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w budgetRead ->
        Cont budgetRead e terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
              UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
                UnaryHistory budgetRead ∧ UnaryHistory terminalRead ∧
                  Cont t w budgetRead ∧ Cont budgetRead e terminalRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier budgetCont terminalCont terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, pUnary, nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tUnary wUnary budgetCont
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary eUnary terminalCont
  exact
    ⟨tUnary, wUnary, qUnary, eUnary, hUnary, cUnary, pUnary, nUnary, budgetUnary,
      terminalUnary, budgetCont, terminalCont, pPkg, terminalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
