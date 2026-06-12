import BEDC.Derived.IntervalDomainUp.NameCertObligations

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IntervalDomainDirectedRefinementCovers
    {L R N W Q E H C P A leftCell rightCell refinementRead directedRead endpointRead
      sealRead : BHist} :
    hsame leftCell L ->
      hsame rightCell R ->
        Cont L R refinementRead ->
          Cont refinementRead N directedRead ->
            Cont W Q endpointRead ->
              Cont directedRead endpointRead sealRead ->
                hsame H A ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row directedRead ∧
                          (hsame row directedRead ∨ hsame row leftCell ∨
                            hsame row rightCell ∨ hsame row N ∨ hsame row W ∨
                              hsame row Q))
                      (fun row : BHist =>
                        hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                          hsame row Q ∨ hsame row E ∨ hsame row sealRead ∨
                            hsame row directedRead)
                      (fun _row : BHist =>
                        hsame leftCell L ∧ hsame rightCell R ∧
                          Cont L R refinementRead ∧ Cont refinementRead N directedRead ∧
                            Cont W Q endpointRead ∧
                              Cont directedRead endpointRead sealRead ∧ hsame H A)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro sameLeft sameRight refinementRoute directedRoute endpointRoute sealRoute sameStructural
  have sourceDirected :
      (fun row : BHist =>
        hsame row directedRead ∧
          (hsame row directedRead ∨ hsame row leftCell ∨ hsame row rightCell ∨
            hsame row N ∨ hsame row W ∨ hsame row Q)) directedRead := by
    exact ⟨hsame_refl directedRead, Or.inl (hsame_refl directedRead)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro directedRead sourceDirected
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeftRows sameRightRows
        exact hsame_trans sameLeftRows sameRightRows
      carrier_respects_equiv := by
        intro _row _other sameRows source
        have sameDirected : hsame _other directedRead :=
          hsame_trans (hsame_symm sameRows) source.left
        exact ⟨sameDirected, Or.inl sameDirected⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨sameLeft, sameRight, refinementRoute, directedRoute, endpointRoute, sealRoute,
          sameStructural⟩
  }

end BEDC.Derived.IntervalDomainUp
