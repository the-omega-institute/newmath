import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zeta_zero_boundary
    {Z S M R Q H C P N zetaRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead N boundaryRead ->
          SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z ∨ hsame row S ∨ hsame row zetaRead ∨ hsame row Q ∨
                  hsame row N ∨ hsame row boundaryRead)
              (fun row : BHist =>
                hsame row boundaryRead ∧ Cont Z S zetaRead ∧
                  Cont zetaRead N boundaryRead ∧ hsame H (append Z S))
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory zetaRead ∧ UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧
                Cont Z S zetaRead ∧ Cont zetaRead N boundaryRead ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute boundaryRoute
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
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryBoundaryRead : UnaryHistory boundaryRead :=
    unary_cont_closed unaryZetaRead unaryN boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, unaryBoundaryRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row zetaRead ∨ hsame row Q ∨
              hsame row N ∨ hsame row boundaryRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z S zetaRead ∧
              Cont zetaRead N boundaryRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceAtBoundary
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, zetaRoute, boundaryRoute, sameH⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, unaryZetaRead, unaryBoundaryRead, sameH,
      zetaRoute, boundaryRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
