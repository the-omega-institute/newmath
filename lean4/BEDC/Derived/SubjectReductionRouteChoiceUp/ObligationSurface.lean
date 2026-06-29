import BEDC.Derived.SubjectReductionRouteChoiceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Cont
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

theorem SubjectReductionRouteChoiceRouteObligationSurface
    {B V O H C P N replay row row' : BHist}
    (route : Cont B V replay)
    (source : SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row)
    (same : hsame row' row) :
    SubjectReductionRouteChoiceObligationRowSpec B V O H C P N B ∧
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N V ∧
        SubjectReductionRouteChoiceObligationRowSpec B V O H C P N O ∧
          Cont B V replay ∧
            SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row' := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have transported :
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row' := by
    cases source with
    | inl sameB =>
        exact Or.inl (hsame_trans same sameB)
    | inr rest =>
        cases rest with
        | inl sameV =>
            exact Or.inr (Or.inl (hsame_trans same sameV))
        | inr rest =>
            cases rest with
            | inl sameO =>
                exact Or.inr (Or.inr (Or.inl (hsame_trans same sameO)))
            | inr rest =>
                cases rest with
                | inl sameH =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans same sameH))))
                | inr rest =>
                    cases rest with
                    | inl sameC =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl (hsame_trans same sameC)))))
                    | inr rest =>
                        cases rest with
                        | inl sameP =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl (hsame_trans same sameP))))))
                        | inr sameN =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr (hsame_trans same sameN))))))
  exact
    ⟨Or.inl (hsame_refl B), Or.inr (Or.inl (hsame_refl V)),
      Or.inr (Or.inr (Or.inl (hsame_refl O))), route, transported⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
