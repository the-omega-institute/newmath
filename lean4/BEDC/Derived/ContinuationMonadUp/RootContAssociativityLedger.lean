import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_root_cont_associativity_ledger [AskSetup] [PackageSetup]
    {A B C f g u H K L N read ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont L N read ->
        Cont read K ledger ->
          PkgSig bundle ledger pkg ->
            UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory C ∧ UnaryHistory K ∧
              UnaryHistory L ∧ UnaryHistory read ∧ UnaryHistory ledger ∧ hsame N L ∧
                Cont L N read ∧ Cont read K ledger ∧ PkgSig bundle ledger pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro carrier rootRead readLedger ledgerPkg
  obtain ⟨unaryA, unaryF, unaryG, unaryU, routeB, routeC, routeK, routeL,
    sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have unaryK : UnaryHistory K :=
    unary_cont_closed unaryF unaryG routeK
  have unaryL : UnaryHistory L :=
    unary_cont_closed unaryK unaryU routeL
  have unaryN : UnaryHistory N :=
    unary_transport unaryL (hsame_symm sameEndpoint)
  have unaryRead : UnaryHistory read :=
    unary_cont_closed unaryL unaryN rootRead
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed unaryRead unaryK readLedger
  exact
    ⟨unaryA, unaryB, unaryC, unaryK, unaryL, unaryRead, unaryLedger, sameEndpoint,
      rootRead, readLedger, ledgerPkg⟩

end BEDC.Derived.ContinuationMonadUp
