import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_source_nonescape
    {Z S M R Q H C P N boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z Q boundaryRead ->
        SemanticNameCert
            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row boundaryRead ∧ Cont Z Q boundaryRead ∧ hsame H (append Z S))
            (fun row : BHist =>
              hsame row boundaryRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory boundaryRead ∧
            hsame H (append Z S) ∧ Cont Z Q boundaryRead ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryZ unaryQ boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z Q boundaryRead ∧ hsame H (append Z S))
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
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
      exact ⟨source.left, boundaryRoute, sameH⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeQ, routeC, routeN⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, boundaryUnary, sameH, boundaryRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
