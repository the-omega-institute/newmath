import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_terminal_rh_refusal_exactness
    {Z S M R Q H C P N terminalSource comparisonRead realRead terminalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S terminalSource ->
        Cont M R comparisonRead ->
          Cont comparisonRead Q realRead ->
            Cont realRead N terminalRead ->
              Cont terminalRead Q rhRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row rhRead ∨ hsame row Z ∨
                        hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q)
                    (fun row : BHist => hsame row rhRead ∧ Cont terminalRead Q rhRead)
                    hsame ∧
                  UnaryHistory terminalSource ∧ UnaryHistory comparisonRead ∧
                    UnaryHistory realRead ∧ UnaryHistory terminalRead ∧ UnaryHistory rhRead ∧
                      hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet sourceRoute comparisonRoute realRoute terminalRoute rhRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have terminalSourceUnary : UnaryHistory terminalSource :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed comparisonUnary routeClosure.left realRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed realUnary routeClosure.right.right.left terminalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed terminalUnary routeClosure.left rhRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row rhRead ∨ hsame row Z ∨
              hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q)
          (fun row : BHist => hsame row rhRead ∧ Cont terminalRead Q rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead ⟨hsame_refl rhRead, rhUnary⟩
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
      exact ⟨source.left, rhRoute⟩
  }
  exact
    ⟨cert, terminalSourceUnary, comparisonUnary, realUnary, terminalUnary, rhUnary,
      sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
