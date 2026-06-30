import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_refusal_package
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead rhRead packageRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              Cont terminalRead Q rhRead ->
                Cont rhRead C packageRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row terminalRead ∨ hsame row rhRead ∨ hsame row packageRead ∨
                          hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q)
                      (fun row : BHist => hsame row packageRead ∧ Cont rhRead C packageRead)
                      hsame ∧
                    UnaryHistory terminalSource ∧ UnaryHistory comparisonRead ∧
                      UnaryHistory realRead ∧ UnaryHistory terminalRead ∧ UnaryHistory rhRead ∧
                        UnaryHistory packageRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                          Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet terminalSourceRoute comparisonRoute realRoute terminalRoute rhRoute packageRoute
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
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed terminalUnary unaryQ rhRoute
  have packageUnary : UnaryHistory packageRead :=
    unary_cont_closed rhUnary unaryC packageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row rhRead ∨ hsame row packageRead ∨
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q)
          (fun row : BHist => hsame row packageRead ∧ Cont rhRead C packageRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead ⟨hsame_refl packageRead, packageUnary⟩
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
      exact ⟨source.left, packageRoute⟩
  }
  exact
    ⟨cert, terminalSourceUnary, comparisonUnary, realUnary, terminalUnary, rhUnary,
      packageUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
