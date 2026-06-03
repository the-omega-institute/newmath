import BEDC.Derived.DecimalExpansionUp.TasteGate

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecimalExpansionRealWindowExhaustion
    {D W V Q R E «prefix» comparison handoff «seal» : BHist} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              Cont D W «prefix» →
                Cont «prefix» V comparison →
                  Cont comparison Q handoff →
                    Cont handoff R «seal» →
                      UnaryHistory «prefix» ∧ UnaryHistory comparison ∧
                        UnaryHistory handoff ∧ UnaryHistory «seal» := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary digitWindow prefixWindow comparisonRoute
    handoffRoute
  have prefixUnary : UnaryHistory «prefix» :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixWindow
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonRoute
  have sealUnary : UnaryHistory «seal» :=
    unary_cont_closed handoffUnary rUnary handoffRoute
  exact ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary⟩

end BEDC.Derived.DecimalExpansionUp
