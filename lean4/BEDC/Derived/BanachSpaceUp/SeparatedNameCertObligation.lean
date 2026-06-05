import BEDC.Derived.BanachSpaceUp.CauchyWindowScope
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_separated_namecert_obligation
    {V N M Q S R E Z H C P L completionWindow terminalWindow separatedWindow : BHist} :
    UnaryHistory Q ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory Z ->
              UnaryHistory L ->
                Cont Q S completionWindow ->
                  Cont completionWindow R terminalWindow ->
                    Cont terminalWindow Z separatedWindow ->
                      SemanticNameCert
                          (fun row : BHist => hsame row separatedWindow ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                              hsame row Z ∨ hsame row L ∨ hsame row completionWindow ∨
                                hsame row terminalWindow ∨ hsame row separatedWindow)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Q S completionWindow ∧
                              Cont completionWindow R terminalWindow ∧
                                Cont terminalWindow Z separatedWindow ∧
                                  hsame row separatedWindow)
                          hsame ∧ UnaryHistory separatedWindow ∧
                        banachSpaceFields (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                          [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory BanachSpaceUp
  intro unaryQ unaryS unaryR _unaryE unaryZ _unaryL completionRoute terminalRoute
    separatedRoute
  have completionUnary : UnaryHistory completionWindow :=
    unary_cont_closed unaryQ unaryS completionRoute
  have terminalUnary : UnaryHistory terminalWindow :=
    unary_cont_closed completionUnary unaryR terminalRoute
  have separatedUnary : UnaryHistory separatedWindow :=
    unary_cont_closed terminalUnary unaryZ separatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row Z ∨
              hsame row L ∨ hsame row completionWindow ∨ hsame row terminalWindow ∨
                hsame row separatedWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q S completionWindow ∧
              Cont completionWindow R terminalWindow ∧ Cont terminalWindow Z separatedWindow ∧
                hsame row separatedWindow)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separatedWindow ⟨hsame_refl separatedWindow, separatedUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, completionRoute, terminalRoute, separatedRoute, source.left⟩
  }
  exact ⟨cert, separatedUnary, rfl⟩

end BEDC.Derived.BanachSpaceUp
