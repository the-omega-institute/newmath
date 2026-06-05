import BEDC.Derived.BanachSpaceUp.CauchyWindowScope
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_namecert_obligations
    {V N M Q S R E Z H C P L normMetric cauchyWindow completionWindow terminalWindow
      separatedWindow : BHist} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory Q ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory Z ->
                  UnaryHistory L ->
                    Cont V N normMetric ->
                      Cont Q S cauchyWindow ->
                        Cont cauchyWindow R completionWindow ->
                          Cont completionWindow E terminalWindow ->
                            Cont terminalWindow Z separatedWindow ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row L ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row V ∨ hsame row N ∨ hsame row M ∨
                                      hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                        hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row L ∨
                                            hsame row separatedWindow)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont Q S cauchyWindow ∧
                                      Cont cauchyWindow R completionWindow ∧
                                        Cont completionWindow E terminalWindow ∧
                                          Cont terminalWindow Z separatedWindow ∧
                                            hsame row L)
                                  hsame ∧ UnaryHistory normMetric ∧
                                UnaryHistory cauchyWindow ∧ UnaryHistory completionWindow ∧
                                  UnaryHistory terminalWindow ∧ UnaryHistory separatedWindow ∧
                                    banachSpaceFields
                                        (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                      [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory BanachSpaceUp
  intro unaryV unaryN unaryQ unaryS unaryR unaryE unaryZ unaryL normRoute cauchyRoute
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row L ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row separatedWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q S cauchyWindow ∧
              Cont cauchyWindow R completionWindow ∧ Cont completionWindow E terminalWindow ∧
                Cont terminalWindow Z separatedWindow ∧ hsame row L)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro L ⟨hsame_refl L, unaryL⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cauchyRoute, completionRoute, terminalRoute, separatedRoute,
          source.left⟩
  }
  exact
    ⟨cert, normUnary, cauchyUnary, completionUnary, terminalUnary, separatedUnary, rfl⟩

end BEDC.Derived.BanachSpaceUp
