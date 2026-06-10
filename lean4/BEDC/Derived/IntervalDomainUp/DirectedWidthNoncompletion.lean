import BEDC.Derived.IntervalDomainUp.RegularCauchyDirectedWidth

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainDirectedWidthNoncompletion
    {_L R N W Q E H C P A widthRead directedRead endpointRead sealRead namedRead
      finiteRoute quotientCut selectedEndpoint ambientCompletion : BHist} :
    UnaryHistory R -> UnaryHistory N -> UnaryHistory W -> UnaryHistory Q -> UnaryHistory E ->
      UnaryHistory A -> UnaryHistory finiteRoute -> Cont R N widthRead ->
        Cont widthRead W directedRead -> Cont directedRead Q endpointRead ->
          Cont endpointRead E sealRead -> Cont sealRead A namedRead ->
            hsame H (append C P) -> hsame namedRead (BHist.e1 finiteRoute) ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row N ∨ hsame row W ∨ hsame row Q ∨
                      hsame row E ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R N widthRead ∧ Cont widthRead W directedRead ∧
                      Cont directedRead Q endpointRead ∧ Cont endpointRead E sealRead ∧
                        Cont sealRead A namedRead ∧ hsame H (append C P))
                  hsame ∧
                (hsame namedRead (BHist.e0 quotientCut) -> False) ∧
                  (hsame namedRead (BHist.e0 selectedEndpoint) -> False) ∧
                    (hsame namedRead (BHist.e0 ambientCompletion) -> False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro hR hN hW hQ hE hA _finiteUnary widthRoute directedRoute endpointRoute sealRoute
    namedRoute historyRoute namedAsFinite
  have widthUnary : UnaryHistory widthRead := unary_cont_closed hR hN widthRoute
  have directedUnary : UnaryHistory directedRead := unary_cont_closed widthUnary hW directedRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed directedUnary hQ endpointRoute
  have sealUnary : UnaryHistory sealRead := unary_cont_closed endpointUnary hE sealRoute
  have namedUnary : UnaryHistory namedRead := unary_cont_closed sealUnary hA namedRoute
  have sourceNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row W ∨ hsame row Q ∨ hsame row E ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R N widthRead ∧ Cont widthRead W directedRead ∧
              Cont directedRead Q endpointRead ∧ Cont endpointRead E sealRead ∧
                Cont sealRead A namedRead ∧ hsame H (append C P))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact
        ⟨source.right, widthRoute, directedRoute, endpointRoute, sealRoute, namedRoute,
          historyRoute⟩
  }
  have noQuotientCut : hsame namedRead (BHist.e0 quotientCut) -> False := by
    intro quotientSame
    exact not_hsame_e1_e0 (hsame_trans (hsame_symm namedAsFinite) quotientSame)
  have noSelectedEndpoint : hsame namedRead (BHist.e0 selectedEndpoint) -> False := by
    intro endpointSame
    exact not_hsame_e1_e0 (hsame_trans (hsame_symm namedAsFinite) endpointSame)
  have noAmbientCompletion : hsame namedRead (BHist.e0 ambientCompletion) -> False := by
    intro completionSame
    exact not_hsame_e1_e0 (hsame_trans (hsame_symm namedAsFinite) completionSame)
  exact ⟨cert, noQuotientCut, noSelectedEndpoint, noAmbientCompletion⟩

end BEDC.Derived.IntervalDomainUp
