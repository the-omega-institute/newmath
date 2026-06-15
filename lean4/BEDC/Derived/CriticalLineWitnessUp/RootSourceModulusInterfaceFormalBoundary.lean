import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_source_modulus_interface_formal_boundary
    {Z S M R Q H C P N sourceRead comparison classifier boundary refusalRead rhRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparison ->
          Cont comparison H classifier ->
            Cont classifier N boundary ->
              Cont N Q refusalRead ->
                Cont refusalRead C rhRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                          hsame row Q ∨ hsame row sourceRead ∨ hsame row comparison ∨
                            hsame row classifier ∨ hsame row boundary ∨ hsame row rhRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont classifier N boundary ∧
                          Cont refusalRead C rhRead ∧ hsame H (append Z S))
                      hsame ∧
                    UnaryHistory boundary ∧ UnaryHistory rhRead ∧
                      hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute classifierRoute boundaryRoute refusalRoute rhRoute
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
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed comparisonUnary unaryH classifierRoute
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed classifierUnary unaryN boundaryRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryC rhRoute
  have sourceAtBoundary :
      (fun row : BHist => hsame row boundary ∧ UnaryHistory row) boundary := by
    exact ⟨hsame_refl boundary, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row sourceRead ∨ hsame row comparison ∨
                hsame row classifier ∨ hsame row boundary ∨ hsame row rhRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont classifier N boundary ∧ Cont refusalRead C rhRead ∧
              hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundary sourceAtBoundary
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, rhRoute, sameH⟩
  }
  exact ⟨cert, boundaryUnary, rhUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
