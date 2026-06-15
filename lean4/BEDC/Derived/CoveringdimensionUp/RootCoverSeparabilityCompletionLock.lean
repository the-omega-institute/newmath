import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverSeparabilityCompletionLock [AskSetup] [PackageSetup]
    {K E C R O L H T P N coverRead refinementRead ledgerRead realRead completionRead
      orderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg ->
      Cont E C coverRead ->
        Cont coverRead R refinementRead ->
          Cont refinementRead L ledgerRead ->
            Cont ledgerRead H realRead ->
              Cont realRead T completionRead ->
                Cont completionRead O orderRead ->
                  PkgSig bundle orderRead pkg ->
                    UnaryHistory ledgerRead ∧ UnaryHistory realRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory orderRead ∧
                        Cont refinementRead L ledgerRead ∧ Cont ledgerRead H realRead ∧
                          Cont realRead T completionRead ∧
                            Cont completionRead O orderRead ∧ PkgSig bundle orderRead pkg := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRoute refinementRoute ledgerRoute realRoute completionRoute orderRoute
    orderPkg
  obtain ⟨_kUnary, eUnary, cUnary, rUnary, oUnary, lUnary, hUnary, tUnary, _pUnary,
    _nUnary, _compactCover, _coverRefinement, _orderLedger, _realCompletion, _pPkg,
    _nPkg⟩ := carrier
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed eUnary cUnary coverRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary rUnary refinementRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refinementUnary lUnary ledgerRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed ledgerUnary hUnary realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary tUnary completionRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed completionUnary oUnary orderRoute
  exact
    ⟨ledgerUnary, realUnary, completionUnary, orderUnary, ledgerRoute, realRoute,
      completionRoute, orderRoute, orderPkg⟩

end BEDC.Derived.CoveringdimensionUp
