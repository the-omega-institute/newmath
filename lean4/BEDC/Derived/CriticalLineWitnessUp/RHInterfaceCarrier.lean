import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_interface_carrier
    {Z S M R Q H C P N stripRead modulusRead rhRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R modulusRead ->
          Cont stripRead modulusRead rhRead ->
            Cont rhRead C boundaryRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont Z S stripRead ∧
                      Cont M R modulusRead)
                  (fun row : BHist =>
                    hsame row boundaryRead ∧ Cont rhRead C boundaryRead)
                  hsame ∧
                UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory rhRead ∧ UnaryHistory boundaryRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute rhRoute boundaryRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed stripUnary modulusUnary rhRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed rhUnary routeClosure.right.left boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont Z S stripRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont rhRead C boundaryRead)
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
      exact ⟨source.left, stripRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, stripUnary, modulusUnary, rhUnary, boundaryUnary, sameH, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
