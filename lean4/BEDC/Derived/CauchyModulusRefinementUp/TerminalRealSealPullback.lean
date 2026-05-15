import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_terminal_real_seal_pullback_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e sealRead ->
        Cont sealRead h terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory sealRead ∧ UnaryHistory terminalRead ∧ Cont m0 m1 u ∧
              Cont u v t ∧ Cont t w q ∧ Cont q e sealRead ∧
                Cont sealRead h terminalRead ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle terminalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier qSealRead sealReadTerminal terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
      hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary qSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary hUnary sealReadTerminal
  exact
    ⟨sealReadUnary, terminalReadUnary, m0m1u, uvt, twq, qSealRead, sealReadTerminal,
      pPkg, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
