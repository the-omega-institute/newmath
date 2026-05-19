import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {A B C f g u H K L N ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont K L ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory f ∧
            UnaryHistory g ∧ UnaryHistory u ∧ UnaryHistory K ∧ UnaryHistory L ∧
              UnaryHistory ledgerRead ∧ Cont A f B ∧ Cont B g C ∧ Cont f g K ∧
                Cont K u L ∧ Cont K L ledgerRead ∧ hsame N L ∧
                  PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier ledgerRoute ledgerPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B := unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C := unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K := unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L := unary_cont_closed unaryK unaryU routeL
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryK unaryL ledgerRoute
  exact
    ⟨unaryA, unaryB, unaryC, unaryF, unaryG, unaryU, unaryK, unaryL,
      unaryLedgerRead, routeB, routeC, routeK, routeL, ledgerRoute,
      sameEndpoint, ledgerPkg⟩

end BEDC.Derived.ContinuationMonadUp
