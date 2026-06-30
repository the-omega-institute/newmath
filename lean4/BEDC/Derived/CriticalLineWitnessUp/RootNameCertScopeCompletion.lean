import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_namecert_scope_completion
    {Z S M R Q H C P N sourceRead comparison classifier boundary zeroRead rootRead
      finalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparison ->
          Cont comparison H classifier ->
            Cont sourceRead classifier boundary ->
              Cont Z S zeroRead ->
                Cont zeroRead Q rootRead ->
                  Cont rootRead N finalRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row boundary ∨ hsame row finalRead ∨ hsame row N)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont sourceRead classifier boundary ∧
                            Cont rootRead N finalRead)
                        hsame ∧
                      UnaryHistory boundary ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute classifierRoute boundaryRoute zeroRoute rootRoute
    finalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed comparisonUnary unaryH classifierRoute
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed sourceUnary classifierUnary boundaryRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed zeroUnary unaryQ rootRoute
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed rootUnary unaryN finalRoute
  have sourceAtFinal : hsame finalRead finalRead ∧ UnaryHistory finalRead :=
    ⟨hsame_refl finalRead, finalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row boundary ∨ hsame row finalRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceRead classifier boundary ∧ Cont rootRead N finalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead sourceAtFinal
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
      exact ⟨source.right, boundaryRoute, finalRoute⟩
  }
  exact ⟨cert, boundaryUnary, finalUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
