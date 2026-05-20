import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_classifier_lock
    {Z S M R Q H C P N sourceRead comparison classifier boundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparison ->
          Cont comparison H classifier ->
            Cont sourceRead classifier boundary ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row boundary ∧ Cont Z S sourceRead ∧ Cont M R comparison)
                  (fun row : BHist =>
                    hsame row boundary ∧ Cont sourceRead classifier boundary)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory comparison ∧
                    UnaryHistory classifier ∧ UnaryHistory boundary ∧
                      hsame comparison Q ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute classifierRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
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
  have sameComparison : hsame comparison Q :=
    cont_deterministic comparisonRoute routeQ
  have sourceAtBoundary :
      (fun row : BHist => hsame row boundary ∧ UnaryHistory row) boundary := by
    exact ⟨hsame_refl boundary, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundary ∧ Cont Z S sourceRead ∧ Cont M R comparison)
          (fun row : BHist =>
            hsame row boundary ∧ Cont sourceRead classifier boundary)
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
      exact ⟨source.left, sourceRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, comparisonUnary,
      classifierUnary, boundaryUnary, sameComparison, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
