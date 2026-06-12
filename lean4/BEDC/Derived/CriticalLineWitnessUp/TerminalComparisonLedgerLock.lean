import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_comparison_ledger_lock
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead ledgerRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              Cont terminalRead H ledgerRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row ledgerRead ∨ hsame row M ∨
                        hsame row R ∨ hsame row Q)
                    (fun row : BHist => hsame row ledgerRead ∧ Cont terminalRead H ledgerRead)
                    hsame ∧
                  UnaryHistory terminalSource ∧ UnaryHistory comparisonRead ∧
                    UnaryHistory realRead ∧ UnaryHistory terminalRead ∧
                      UnaryHistory ledgerRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalRoute comparisonRoute realRoute terminalReadRoute ledgerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have terminalSourceUnary : UnaryHistory terminalSource :=
    unary_cont_closed unaryZ unaryS terminalRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed comparisonUnary unaryQ realRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary unaryN terminalReadRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed terminalReadUnary unaryH ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row ledgerRead ∨ hsame row M ∨ hsame row R ∨
              hsame row Q)
          (fun row : BHist => hsame row ledgerRead ∧ Cont terminalRead H ledgerRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact
    ⟨cert, terminalSourceUnary, comparisonUnary, realUnary, terminalReadUnary, ledgerUnary,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
