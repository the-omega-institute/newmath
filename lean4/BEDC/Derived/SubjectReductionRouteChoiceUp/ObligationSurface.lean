import BEDC.Derived.SubjectReductionRouteChoiceUp.TasteGate

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SubjectReductionRouteChoiceObligationSurface (B V O H C P N : BHist) :
    SemanticNameCert
        (SubjectReductionRouteChoiceObligationRowSpec B V O H C P N)
        (SubjectReductionRouteChoiceObligationRowSpec B V O H C P N)
        (SubjectReductionRouteChoiceObligationRowSpec B V O H C P N)
        hsame ∧
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N B ∧
        SubjectReductionRouteChoiceObligationRowSpec B V O H C P N V ∧
          SubjectReductionRouteChoiceObligationRowSpec B V O H C P N O := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact
    ⟨SubjectReductionRouteChoiceObligations B V O H C P N,
      Or.inl (hsame_refl B),
      Or.inr (Or.inl (hsame_refl V)),
      Or.inr (Or.inr (Or.inl (hsame_refl O)))⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
