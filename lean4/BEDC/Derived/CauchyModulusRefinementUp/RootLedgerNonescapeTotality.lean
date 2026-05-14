import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_ledger_nonescape_totality
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e ledgerRead ->
        Cont ledgerRead h publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory h ∧ UnaryHistory ledgerRead ∧
              UnaryHistory publicRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
                Cont q e ledgerRead ∧ Cont ledgerRead h publicRead ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier qLedger ledgerPublic publicPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed qUnary eUnary qLedger
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary hUnary ledgerPublic
  exact
    ⟨qUnary, eUnary, hUnary, ledgerUnary, publicUnary, m0m1u, uvt, twq, qLedger,
      ledgerPublic, pPkg, publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
