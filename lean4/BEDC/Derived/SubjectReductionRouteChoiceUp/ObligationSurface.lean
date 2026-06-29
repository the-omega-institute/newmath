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

theorem SubjectReductionRouteChoiceTypePreservationWindow
    {B V O H C P N replay typeWindow : BHist}
    (route : Cont B V replay)
    (window : Cont replay O typeWindow) :
    SemanticNameCert
        (fun row : BHist => hsame row typeWindow)
        (fun row : BHist =>
          hsame row B ∨ hsame row V ∨ hsame row O ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row typeWindow)
        (fun row : BHist =>
          hsame row typeWindow ∧ Cont B V replay ∧ Cont replay O typeWindow)
        hsame ∧
      Cont B V replay ∧ Cont replay O typeWindow := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row typeWindow)
          (fun row : BHist =>
            hsame row B ∨ hsame row V ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row typeWindow)
          (fun row : BHist =>
            hsame row typeWindow ∧ Cont B V replay ∧ Cont replay O typeWindow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro typeWindow (hsame_refl typeWindow)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, route, window⟩
  }
  exact ⟨cert, route, window⟩

theorem SubjectReductionRouteChoiceObstructionBoundary
    {B V O H C P N blocked : BHist}
    (obstructionRoute : Cont O H blocked) :
    SemanticNameCert
        (fun row : BHist => hsame row O)
        (SubjectReductionRouteChoiceObligationRowSpec B V O H C P N)
        (fun row : BHist => hsame row O ∨ hsame row H ∨ Cont O H blocked)
        hsame ∧
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N O ∧
        Cont O H blocked := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row O)
          (SubjectReductionRouteChoiceObligationRowSpec B V O H C P N)
          (fun row : BHist => hsame row O ∨ hsame row H ∨ Cont O H blocked)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro O (hsame_refl O)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source))
    ledger_sound := by
      intro _row _source
      exact Or.inr (Or.inr obstructionRoute)
  }
  exact
    ⟨cert, Or.inr (Or.inr (Or.inl (hsame_refl O))), obstructionRoute⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
