import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_terminal_seal_factorization [AskSetup] [PackageSetup]
    {q s g d r w h c p n terminalRead completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont r w terminalRead →
        Cont terminalRead c completionConsumer →
          PkgSig bundle completionConsumer pkg →
            UnaryHistory terminalRead ∧ UnaryHistory completionConsumer ∧
              Cont r w terminalRead ∧ Cont terminalRead c completionConsumer ∧
                PkgSig bundle p pkg ∧ PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier terminalRoute completionRoute completionPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed rUnary wUnary terminalRoute
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed terminalUnary cUnary completionRoute
  exact
    ⟨terminalUnary, completionUnary, terminalRoute, completionRoute, pPkg, completionPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
