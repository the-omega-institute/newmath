import BEDC.Derived.DyadicApproximationUp.L10RealCompletionSiblingRoute

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_real_completion_exit_criterion
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell validatedEnclosure sealRow
      tailBudget diagonalRead budgetRead streamWindow regSeqReadback dyadicLedger
      realCompletionSeal completionRoute hubRead admittedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance meshCell ->
                    Cont meshCell terminalProvenance validatedEnclosure ->
                      Cont terminalLedger terminalProvenance sealRow ->
                        Cont sealRow terminalProvenance tailBudget ->
                          Cont terminalWindow sealRow diagonalRead ->
                            Cont tailBudget diagonalRead budgetRead ->
                              Cont terminalWindow terminalProvenance streamWindow ->
                                Cont streamWindow terminalProvenance regSeqReadback ->
                                  Cont regSeqReadback terminalProvenance dyadicLedger ->
                                    Cont dyadicLedger terminalProvenance realCompletionSeal ->
                                      Cont budgetRead terminalProvenance completionRoute ->
                                        Cont completionRoute terminalProvenance hubRead ->
                                          Cont hubRead terminalProvenance admittedRead ->
                                            PkgSig bundle tailBudget pkg ->
                                              PkgSig bundle diagonalRead pkg ->
                                                PkgSig bundle budgetRead pkg ->
                                                  PkgSig bundle completionRoute pkg ->
                                                    PkgSig bundle hubRead pkg ->
                                                      PkgSig bundle admittedRead pkg ->
                                                        UnaryHistory streamWindow ∧
                                                          UnaryHistory regSeqReadback ∧
                                                            UnaryHistory dyadicLedger ∧
                                                              UnaryHistory realCompletionSeal ∧
                                                                UnaryHistory completionRoute ∧
                                                                  UnaryHistory hubRead ∧
                                                                    UnaryHistory admittedRead ∧
                                                                      PkgSig bundle
                                                                        admittedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance terminalWindowRoute
  intro terminalProvenanceRoute meshCellRoute enclosureRoute sealRoute tailBudgetRoute
  intro diagonalRoute budgetRoute streamWindowRoute regSeqRoute dyadicLedgerRoute
  intro realCompletionSealRoute completionRouteCont hubReadCont admittedReadCont
  intro tailPkg diagonalPkg budgetPkg completionPkg hubPkg admittedPkg
  have hubRoute :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory streamWindow ∧ UnaryHistory regSeqReadback ∧
          UnaryHistory dyadicLedger ∧ UnaryHistory realCompletionSeal ∧
            UnaryHistory completionRoute ∧ UnaryHistory hubRead ∧
              PkgSig bundle hubRead pkg :=
    DyadicApproximationCarrier_top_hub_l10_sibling_route carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalWindowRoute terminalProvenanceRoute
      meshCellRoute enclosureRoute sealRoute tailBudgetRoute diagonalRoute budgetRoute
      streamWindowRoute regSeqRoute dyadicLedgerRoute realCompletionSealRoute
      completionRouteCont hubReadCont tailPkg diagonalPkg budgetPkg completionPkg hubPkg
  have terminalCarrier :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg :=
    hubRoute.left
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, _terminalWindowUnary,
    _terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
    _terminalProvenanceRoute, _terminalPkg⟩ := terminalCarrier
  have streamUnary : UnaryHistory streamWindow :=
    hubRoute.right.left
  have regSeqUnary : UnaryHistory regSeqReadback :=
    hubRoute.right.right.left
  have dyadicLedgerUnary : UnaryHistory dyadicLedger :=
    hubRoute.right.right.right.left
  have realCompletionSealUnary : UnaryHistory realCompletionSeal :=
    hubRoute.right.right.right.right.left
  have completionUnary : UnaryHistory completionRoute :=
    hubRoute.right.right.right.right.right.left
  have hubUnary : UnaryHistory hubRead :=
    hubRoute.right.right.right.right.right.right.left
  have admittedUnary : UnaryHistory admittedRead :=
    unary_cont_closed hubUnary terminalProvenanceUnary admittedReadCont
  exact
    ⟨streamUnary, regSeqUnary, dyadicLedgerUnary, realCompletionSealUnary, completionUnary,
      hubUnary, admittedUnary, admittedPkg⟩

end BEDC.Derived.DyadicApproximationUp
