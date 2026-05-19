import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_boundary_obligation_surface
    {Z S M R Q H C P N zeroRead comparisonRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R comparisonRead ->
          Cont comparisonRead H boundaryRead ->
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row boundaryRead ∧ Cont Z S zeroRead ∧ Cont M R comparisonRead)
                (fun row : BHist => hsame row boundaryRead ∧ Cont comparisonRead H boundaryRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory comparisonRead ∧ UnaryHistory boundaryRead ∧
                hsame H (append Z S) ∧ Cont Z S zeroRead ∧ Cont M R comparisonRead ∧
                  Cont comparisonRead H boundaryRead ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute comparisonRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have sameZeroH : hsame zeroRead H :=
    zeroRoute.trans sameH.symm
  have unaryH : UnaryHistory H :=
    unary_transport zeroUnary sameZeroH
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed comparisonUnary unaryH boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z S zeroRead ∧ Cont M R comparisonRead)
          (fun row : BHist => hsame row boundaryRead ∧ Cont comparisonRead H boundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceAtBoundary
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, zeroRoute, comparisonRoute⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨hsame_refl boundaryRead, boundaryRoute⟩
  }
  exact
    ⟨cert, zeroUnary, comparisonUnary, boundaryUnary, sameH, zeroRoute, comparisonRoute,
      boundaryRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
