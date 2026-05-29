import BEDC.Derived.DecimalExpansionUp.TasteGate

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecimalExpansionFinitePrefixCompleteness
    {D W V Q R E H C P N «prefix» comparison handoff «seal» publicRead namedRead : BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    Cont D W «prefix» ->
                      Cont «prefix» V comparison ->
                        Cont comparison Q handoff ->
                          Cont handoff R «seal» ->
                            Cont «seal» H publicRead ->
                              Cont publicRead C namedRead ->
                                UnaryHistory «prefix» ∧ UnaryHistory comparison ∧
                                  UnaryHistory handoff ∧ UnaryHistory «seal» ∧
                                    UnaryHistory publicRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary _eUnary hUnary cUnary digitWindow
    prefixPlace comparisonDyadic handoffReal sealTransport publicName
  have prefixUnary : UnaryHistory «prefix» :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonDyadic
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary rUnary handoffReal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary sealTransport
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed publicUnary cUnary publicName
  exact ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary, publicUnary, namedUnary⟩

end BEDC.Derived.DecimalExpansionUp
