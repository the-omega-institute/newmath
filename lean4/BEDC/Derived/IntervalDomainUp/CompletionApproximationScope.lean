import BEDC.Derived.IntervalDomainUp.NameCertObligations

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IntervalDomainCompletionApproximationScope
    {L R N W Q E H C P A refinementRead directedRead endpointRead sealRead
      namedRead : BHist} :
    Cont L R refinementRead ->
      Cont refinementRead N directedRead ->
        Cont W Q endpointRead ->
          Cont directedRead endpointRead sealRead ->
            Cont sealRead A namedRead ->
              hsame H C ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row namedRead ∧
                        (hsame row E ∨ hsame row sealRead ∨ hsame row namedRead))
                    (fun row : BHist =>
                      hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                        hsame row Q ∨ hsame row E ∨ hsame row sealRead ∨
                          hsame row namedRead)
                    (fun _row : BHist =>
                      Cont L R refinementRead ∧ Cont refinementRead N directedRead ∧
                        Cont W Q endpointRead ∧
                          Cont directedRead endpointRead sealRead ∧
                            Cont sealRead A namedRead ∧ hsame H C)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro refinementRoute directedRoute endpointRoute sealRoute namedRoute structuralSame
  have sourceNamed :
      (fun row : BHist =>
        hsame row namedRead ∧
          (hsame row E ∨ hsame row sealRead ∨ hsame row namedRead)) namedRead := by
    exact ⟨hsame_refl namedRead, Or.inr (Or.inr (hsame_refl namedRead))⟩
  exact {
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
            Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) source.left))⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨refinementRoute, directedRoute, endpointRoute, sealRoute, namedRoute,
          structuralSame⟩
  }

end BEDC.Derived.IntervalDomainUp
