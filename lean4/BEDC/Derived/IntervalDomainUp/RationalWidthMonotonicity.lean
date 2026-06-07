import BEDC.Derived.IntervalDomainUp.NameCertObligations

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem IntervalDomainRationalWidthMonotonicity
    {L R N W Q E H _C _P A locatedCell rationalBudget nestedRead tightenedBudget
      endpointRead sealRead : BHist} :
    hsame locatedCell L →
      hsame rationalBudget R →
        Cont L R nestedRead →
          Cont nestedRead N tightenedBudget →
            Cont W Q endpointRead →
              Cont tightenedBudget endpointRead sealRead →
                hsame H A →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row tightenedBudget ∧
                          (hsame row tightenedBudget ∨ hsame row rationalBudget ∨
                            hsame row N ∨ hsame row W ∨ hsame row Q))
                      (fun row : BHist =>
                        hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                          hsame row Q ∨ hsame row E ∨ hsame row sealRead ∨
                            hsame row tightenedBudget)
                      (fun _row : BHist =>
                        hsame locatedCell L ∧ hsame rationalBudget R ∧
                          Cont L R nestedRead ∧ Cont nestedRead N tightenedBudget ∧
                            Cont W Q endpointRead ∧
                              Cont tightenedBudget endpointRead sealRead ∧ hsame H A)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro sameLocated sameRational nestedRoute tightenedRoute endpointRoute sealRoute
    sameStructural
  have sourceTightened :
      (fun row : BHist =>
        hsame row tightenedBudget ∧
          (hsame row tightenedBudget ∨ hsame row rationalBudget ∨ hsame row N ∨
            hsame row W ∨ hsame row Q)) tightenedBudget := by
    exact ⟨hsame_refl tightenedBudget, Or.inl (hsame_refl tightenedBudget)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro tightenedBudget sourceTightened
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
        have sameTightened : hsame _other tightenedBudget :=
          hsame_trans (hsame_symm sameRows) source.left
        exact ⟨sameTightened, Or.inl sameTightened⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨sameLocated, sameRational, nestedRoute, tightenedRoute, endpointRoute, sealRoute,
          sameStructural⟩
  }

end BEDC.Derived.IntervalDomainUp
