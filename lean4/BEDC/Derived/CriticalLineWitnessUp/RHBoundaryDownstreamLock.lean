import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_boundary_downstream_lock
    {Z S M R Q H C P N comparisonRead refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S comparisonRead ->
        Cont N Q refusalRead ->
          Cont refusalRead C boundaryRead ->
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row boundaryRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S comparisonRead ∧ Cont N Q refusalRead ∧
                    Cont refusalRead C boundaryRead)
                hsame ∧
              UnaryHistory comparisonRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet comparisonRoute refusalRoute boundaryRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  obtain ⟨unaryQ, unaryC, unaryN, _sameHAgain⟩ :=
    routeClosure
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryZ unaryS comparisonRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed refusalUnary unaryC boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S comparisonRead ∧ Cont N Q refusalRead ∧
              Cont refusalRead C boundaryRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead (And.intro (hsame_refl boundaryRead) boundaryUnary)
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
        intro _row _other sameRows sourceRow
        exact
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, comparisonRoute, refusalRoute, boundaryRoute⟩
  }
  exact ⟨cert, comparisonUnary, refusalUnary, boundaryUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
