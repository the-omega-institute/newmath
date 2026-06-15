import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_consumer_exhaustion
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead consumerRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              Cont terminalRead C consumerRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row consumerRead ∨ hsame row N)
                    (fun row : BHist =>
                      hsame row consumerRead ∧ Cont terminalRead C consumerRead ∧
                        Cont realRead N terminalRead)
                    hsame ∧
                  UnaryHistory terminalRead ∧ UnaryHistory consumerRead ∧
                    hsame H (append Z S) ∧ Cont Z S terminalSource ∧
                      Cont M R comparisonRead ∧ Cont comparisonRead Q realRead ∧
                        Cont realRead N terminalRead ∧
                          Cont terminalRead C consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalSourceRoute comparisonRoute realRoute terminalRoute consumerRoute
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
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed comparisonUnary unaryQ realRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary unaryN terminalRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed terminalUnary unaryC consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead ∧ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row consumerRead ∨ hsame row N)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont terminalRead C consumerRead ∧
              Cont realRead N terminalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact ⟨source.left, consumerRoute, terminalRoute⟩
  }
  exact
    ⟨cert, terminalUnary, consumerUnary, sameH, terminalSourceRoute, comparisonRoute,
      realRoute, terminalRoute, consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
