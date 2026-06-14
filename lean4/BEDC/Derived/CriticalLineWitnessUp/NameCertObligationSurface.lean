import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_namecert_obligation_surface
    {Z S M R Q H C P N sourceRead budgetRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead H budgetRead ->
          Cont N Q refusalRead ->
            SemanticNameCert
                (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row sourceRead ∨ hsame row budgetRead ∨
                    hsame row refusalRead ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont sourceRead H budgetRead ∧ Cont N Q refusalRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                  UnaryHistory sourceRead ∧ UnaryHistory budgetRead ∧
                    UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                      Cont Z S sourceRead ∧ Cont sourceRead H budgetRead ∧
                        Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                          Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute budgetRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    routeClosure.left
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    routeClosure.right.left
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sourceUnary unaryH budgetRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row budgetRead ∨
              hsame row refusalRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceRead H budgetRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
      exact ⟨source.right, budgetRoute, refusalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN,
      sourceUnary, budgetUnary, refusalUnary, sameH, sourceRoute, budgetRoute, routeQ,
      routeC, routeN, refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
