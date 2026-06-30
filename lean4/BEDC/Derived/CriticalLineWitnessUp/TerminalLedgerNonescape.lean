import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_ledger_nonescape
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead ledgerRead
      nonescapeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              Cont terminalRead H ledgerRead ->
                Cont ledgerRead C nonescapeRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row nonescapeRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row terminalRead ∨ hsame row ledgerRead ∨
                          hsame row nonescapeRead ∨ hsame row M ∨ hsame row R ∨ hsame row Q)
                      (fun row : BHist =>
                        hsame row nonescapeRead ∧ Cont ledgerRead C nonescapeRead)
                      hsame ∧
                    UnaryHistory terminalSource ∧ UnaryHistory comparisonRead ∧
                      UnaryHistory realRead ∧ UnaryHistory terminalRead ∧
                        UnaryHistory ledgerRead ∧ UnaryHistory nonescapeRead ∧
                          hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalRoute comparisonRoute realRoute terminalReadRoute ledgerRoute
    nonescapeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have terminalSourceUnary : UnaryHistory terminalSource :=
    unary_cont_closed unaryZ unaryS terminalRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed comparisonReadUnary unaryQ realRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed realReadUnary unaryN terminalReadRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed terminalReadUnary unaryH ledgerRoute
  have nonescapeReadUnary : UnaryHistory nonescapeRead :=
    unary_cont_closed ledgerReadUnary unaryC nonescapeRoute
  have sourceAtNonescape : hsame nonescapeRead nonescapeRead ∧ UnaryHistory nonescapeRead :=
    ⟨hsame_refl nonescapeRead, nonescapeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nonescapeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row ledgerRead ∨ hsame row nonescapeRead ∨
              hsame row M ∨ hsame row R ∨ hsame row Q)
          (fun row : BHist => hsame row nonescapeRead ∧ Cont ledgerRead C nonescapeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nonescapeRead sourceAtNonescape
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, nonescapeRoute⟩
  }
  exact
    ⟨cert, terminalSourceUnary, comparisonReadUnary, realReadUnary, terminalReadUnary,
      ledgerReadUnary, nonescapeReadUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
