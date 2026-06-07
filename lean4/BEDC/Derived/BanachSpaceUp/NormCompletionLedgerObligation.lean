import BEDC.Derived.BanachSpaceUp.CauchyWindowScope

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_norm_completion_ledger_obligation
    {V N M Q S R E Z H C P L normMetric cauchyWindow completionWindow terminalWindow
      separatedWindow : BHist} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory Q ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory Z ->
                  Cont V N normMetric ->
                    Cont Q S cauchyWindow ->
                      Cont cauchyWindow R completionWindow ->
                        Cont completionWindow E terminalWindow ->
                          Cont terminalWindow Z separatedWindow ->
                            UnaryHistory normMetric ∧ UnaryHistory cauchyWindow ∧
                              UnaryHistory completionWindow ∧ UnaryHistory terminalWindow ∧
                                UnaryHistory separatedWindow ∧
                                  hsame normMetric (append V N) ∧
                                    hsame terminalWindow (append completionWindow E) ∧
                                      hsame separatedWindow (append terminalWindow Z) ∧
                                        banachSpaceFields
                                            (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                          [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame append BanachSpaceUp
  intro unaryV unaryN unaryQ unaryS unaryR unaryE unaryZ normRoute cauchyRoute
    completionRoute terminalRoute separatedRoute
  have normUnary : UnaryHistory normMetric :=
    unary_cont_closed unaryV unaryN normRoute
  have cauchyUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed unaryQ unaryS cauchyRoute
  have completionUnary : UnaryHistory completionWindow :=
    unary_cont_closed cauchyUnary unaryR completionRoute
  have terminalUnary : UnaryHistory terminalWindow :=
    unary_cont_closed completionUnary unaryE terminalRoute
  have separatedUnary : UnaryHistory separatedWindow :=
    unary_cont_closed terminalUnary unaryZ separatedRoute
  have normExact : hsame normMetric (append V N) := by
    cases normRoute
    exact hsame_refl _
  have terminalExact : hsame terminalWindow (append completionWindow E) := by
    cases terminalRoute
    exact hsame_refl _
  have separatedExact : hsame separatedWindow (append terminalWindow Z) := by
    cases separatedRoute
    exact hsame_refl _
  exact
    ⟨normUnary, cauchyUnary, completionUnary, terminalUnary, separatedUnary, normExact,
      terminalExact, separatedExact, rfl⟩

end BEDC.Derived.BanachSpaceUp
