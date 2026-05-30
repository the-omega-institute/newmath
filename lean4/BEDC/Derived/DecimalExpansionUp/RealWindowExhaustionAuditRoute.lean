import BEDC.Derived.DecimalExpansionUp.TasteGate

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecimalExpansionRealWindowExhaustionAuditRoute
    {D W V Q R E H C P N «prefix» comparison handoff «seal» transported replayed sourced named :
      BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont D W «prefix» ->
                        Cont «prefix» V comparison ->
                          Cont comparison Q handoff ->
                            Cont handoff R «seal» ->
                              Cont «seal» H transported ->
                                Cont transported C replayed ->
                                  Cont replayed P sourced ->
                                    Cont sourced N named ->
                                      UnaryHistory «prefix» ∧ UnaryHistory comparison ∧
                                        UnaryHistory handoff ∧ UnaryHistory «seal» ∧
                                          UnaryHistory transported ∧ UnaryHistory replayed ∧
                                            UnaryHistory sourced ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary hUnary cUnary pUnary nUnary digitWindow
    prefixWindow comparisonRoute handoffRoute sealTransport transportReplay replaySource sourceName
  have prefixUnary : UnaryHistory «prefix» :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixWindow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonRoute
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary rUnary handoffRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary hUnary sealTransport
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary cUnary transportReplay
  have sourcedUnary : UnaryHistory sourced :=
    unary_cont_closed replayedUnary pUnary replaySource
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sourcedUnary nUnary sourceName
  exact
    ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary, transportedUnary, replayedUnary,
      sourcedUnary, namedUnary⟩

end BEDC.Derived.DecimalExpansionUp
