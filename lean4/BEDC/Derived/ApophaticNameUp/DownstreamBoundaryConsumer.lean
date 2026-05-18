import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameDownstreamBoundaryConsumer [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow boundaryRead consumerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow boundaryRead →
        Cont boundaryRead route consumerRead →
          PkgSig bundle consumerRead pkg →
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
              UnaryHistory ledger ∧ UnaryHistory nameRow ∧ UnaryHistory boundaryRead ∧
                UnaryHistory consumerRead ∧ Cont socket request gate ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow boundaryRead ∧
                    Cont boundaryRead route consumerRead ∧ hsame ledger (append request gate) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier boundaryRoute consumerRoute consumerPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
      _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed ledgerUnary nameRowUnary boundaryRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed boundaryUnary routeUnary consumerRoute
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, nameRowUnary, boundaryUnary,
      consumerUnary, socketRequestGate, gateLedgerNameRow, boundaryRoute, consumerRoute,
      ledgerSameRequestGate, provenancePkg, consumerPkg⟩

end BEDC.Derived.ApophaticNameUp
