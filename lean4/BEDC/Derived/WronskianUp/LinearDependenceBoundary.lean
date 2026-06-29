import BEDC.Derived.WronskianUp.TasteGate

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Hist

theorem WronskianCarrier_linear_dependence_boundary (x : WronskianUp) :
    ∃ F D J Omega S R E H C P N : BHist,
      x = WronskianUp.mk F D J Omega S R E H C P N ∧
        WronskianObligationRowSpec F D J Omega S R E H C P N J ∧
          WronskianObligationRowSpec F D J Omega S R E H C P N Omega ∧
            WronskianObligationRowSpec F D J Omega S R E H C P N E := by
  -- BEDC touchpoint anchor: BHist hsame
  cases x with
  | mk F D J Omega S R E H C P N =>
      refine ⟨F, D, J, Omega, S, R, E, H, C, P, N, ?_⟩
      constructor
      · rfl
      · constructor
        · exact Or.inr (Or.inr (Or.inl (hsame_refl J)))
        · constructor
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl Omega))))
          · exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl (hsame_refl E)))))))

end BEDC.Derived.WronskianUp
