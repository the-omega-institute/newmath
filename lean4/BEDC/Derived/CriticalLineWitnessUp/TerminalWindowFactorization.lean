import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_window_factorization
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row terminalRead ∧ Cont Z S terminalSource ∧
                      Cont M R comparisonRead)
                  (fun row : BHist =>
                    hsame row terminalRead ∧ Cont realRead N terminalRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory N ∧ UnaryHistory terminalSource ∧
                    UnaryHistory comparisonRead ∧ UnaryHistory realRead ∧
                      UnaryHistory terminalRead ∧ hsame H (append Z S) ∧
                        Cont Z S terminalSource ∧ Cont M R comparisonRead ∧
                          Cont comparisonRead Q realRead ∧ Cont realRead N terminalRead ∧
                            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalSourceRoute comparisonRoute realRoute terminalRoute
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
    unary_cont_closed unaryZ unaryS terminalSourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed comparisonUnary unaryQ realRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary unaryN terminalRoute
  have sourceAtTerminal : hsame terminalRead terminalRead ∧ UnaryHistory terminalRead :=
    ⟨hsame_refl terminalRead, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∧ Cont Z S terminalSource ∧ Cont M R comparisonRead)
          (fun row : BHist =>
            hsame row terminalRead ∧ Cont realRead N terminalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead sourceAtTerminal
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
      exact ⟨source.left, terminalSourceRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryN, terminalSourceUnary,
      comparisonUnary, realUnary, terminalUnary, sameH, terminalSourceRoute,
      comparisonRoute, realRoute, terminalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
