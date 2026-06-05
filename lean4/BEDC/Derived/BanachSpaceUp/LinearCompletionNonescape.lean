import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BanachSpaceLinearCompletionNonescape
    {V N M Q S R E Z H C P L cauchyWindow completionWindow terminalSeal
      separatedRead : BHist} :
    UnaryHistory Q ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory Z ->
              Cont Q S cauchyWindow ->
                Cont cauchyWindow R completionWindow ->
                  Cont completionWindow E terminalSeal ->
                    Cont terminalSeal Z separatedRead ->
                      UnaryHistory cauchyWindow ∧
                        UnaryHistory completionWindow ∧
                          UnaryHistory terminalSeal ∧
                            UnaryHistory separatedRead ∧
                              banachSpaceFields
                                  (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BanachSpaceUp
  intro qUnary sUnary rUnary eUnary zUnary cauchyRoute completionRoute terminalRoute
    separatedRoute
  have cauchyUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionWindow :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have terminalUnary : UnaryHistory terminalSeal :=
    unary_cont_closed completionUnary eUnary terminalRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed terminalUnary zUnary separatedRoute
  exact ⟨cauchyUnary, completionUnary, terminalUnary, separatedUnary, rfl⟩

end BEDC.Derived.BanachSpaceUp
