import BEDC.Derived.SubjectReductionRouteChoiceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

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

theorem SubjectReductionRouteChoiceBlockedEdgeNonescape
    {B V O H C P N blockedRead : BHist}
    (obstructionRoute : Cont O H blockedRead) :
    SemanticNameCert
        (fun row : BHist => hsame row blockedRead)
        (fun row : BHist =>
          SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
            hsame row blockedRead)
        (fun row : BHist => hsame row blockedRead ∧ Cont O H blockedRead)
        hsame ∧
      SubjectReductionRouteChoiceObligationRowSpec B V O H C P N O ∧
        Cont O H blockedRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row blockedRead)
          (fun row : BHist =>
            SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
              hsame row blockedRead)
          (fun row : BHist => hsame row blockedRead ∧ Cont O H blockedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro blockedRead (hsame_refl blockedRead)
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
      exact Or.inr source
    ledger_sound := by
      intro _row source
      exact ⟨source, obstructionRoute⟩
  }
  exact
    ⟨cert, Or.inr (Or.inr (Or.inl (hsame_refl O))), obstructionRoute⟩

theorem SubjectReductionRouteChoiceCarrier_blocked_edge_nonescape
    {B V O H C P N blocked replayed : BHist} :
    UnaryHistory O →
      UnaryHistory H →
        UnaryHistory C →
          Cont O H blocked →
            Cont blocked C replayed →
              SemanticNameCert
                  (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row V ∨ hsame row O ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row blocked ∨
                        hsame row replayed)
                  (fun row : BHist =>
                    hsame row replayed ∧ Cont O H blocked ∧ Cont blocked C replayed)
                  hsame ∧
                UnaryHistory blocked ∧ UnaryHistory replayed := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro oUnary hUnary cUnary blockedRoute replayRoute
  have blockedUnary : UnaryHistory blocked :=
    unary_cont_closed oUnary hUnary blockedRoute
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed blockedUnary cUnary replayRoute
  have sourceReplayed :
      (fun row : BHist => hsame row replayed ∧ UnaryHistory row) replayed := by
    exact ⟨hsame_refl replayed, replayedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayed ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row V ∨ hsame row O ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row blocked ∨
                hsame row replayed)
          (fun row : BHist =>
            hsame row replayed ∧ Cont O H blocked ∧ Cont blocked C replayed)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayed sourceReplayed
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, blockedRoute, replayRoute⟩
  }
  exact ⟨cert, blockedUnary, replayedUnary⟩

theorem SubjectReductionRouteChoiceObstructionRouteExhaustion
    {B V O H C P N bundleRead obstructionRead publicRead : BHist}
    (bundleRoute : Cont B V bundleRead)
    (obstructionRoute : Cont O H obstructionRead)
    (publicRoute : Cont bundleRead obstructionRead publicRead) :
    SemanticNameCert
        (fun row : BHist => hsame row publicRead)
        (fun row : BHist =>
          SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
            hsame row bundleRead ∨ hsame row obstructionRead ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont B V bundleRead ∧ Cont O H obstructionRead ∧
            Cont bundleRead obstructionRead publicRead)
        hsame ∧
      Cont B V bundleRead ∧
        Cont O H obstructionRead ∧
          Cont bundleRead obstructionRead publicRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist =>
            SubjectReductionRouteChoiceObligationRowSpec B V O H C P N row ∨
              hsame row bundleRead ∨ hsame row obstructionRead ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont B V bundleRead ∧ Cont O H obstructionRead ∧
              Cont bundleRead obstructionRead publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead (hsame_refl publicRead)
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
      exact Or.inr (Or.inr (Or.inr source))
    ledger_sound := by
      intro _row source
      exact ⟨source, bundleRoute, obstructionRoute, publicRoute⟩
  }
  exact ⟨cert, bundleRoute, obstructionRoute, publicRoute⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
