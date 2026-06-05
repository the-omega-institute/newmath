import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_cauchy_window_scope
    {V N M Q S R E Z H C P L cauchyWindow completionWindow terminalWindow : BHist} :
    UnaryHistory Q ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory E ->
            Cont Q S cauchyWindow ->
              Cont cauchyWindow R completionWindow ->
                Cont completionWindow E terminalWindow ->
                  UnaryHistory cauchyWindow ∧
                    UnaryHistory completionWindow ∧
                      UnaryHistory terminalWindow ∧
                        Cont Q S cauchyWindow ∧
                          Cont cauchyWindow R completionWindow ∧
                            Cont completionWindow E terminalWindow ∧
                              banachSpaceFields (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BanachSpaceUp
  intro qUnary sUnary rUnary eUnary cauchyRoute completionRoute terminalRoute
  have cauchyUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionWindow :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have terminalUnary : UnaryHistory terminalWindow :=
    unary_cont_closed completionUnary eUnary terminalRoute
  exact
    ⟨cauchyUnary, completionUnary, terminalUnary, cauchyRoute, completionRoute,
      terminalRoute, rfl⟩

end BEDC.Derived.BanachSpaceUp
