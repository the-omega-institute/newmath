import BEDC.Derived.FableBranchWitnessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FableBranchWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FableBranchWitnessCarrier_selector_exposure
    {h m r E A H C P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row m ∧
          ∃ W : FableBranchWitnessUp,
            fableBranchWitnessToEventFlow W =
              fableBranchWitnessToEventFlow (FableBranchWitnessUp.mk h m r E A H C P N))
      (fun row : BHist =>
        hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
          hsame row C ∨ hsame row N)
      (fun row : BHist =>
        hsame row m ∧ fableBranchWitnessEncodeBHist BHist.Empty = ([] : List BMark))
      hsame := by
  -- BEDC touchpoint anchor: BHist BMark hsame SemanticNameCert
  let W := FableBranchWitnessUp.mk h m r E A H C P N
  have sourceMark :
      (fun row : BHist =>
        hsame row m ∧
          ∃ W : FableBranchWitnessUp,
            fableBranchWitnessToEventFlow W =
              fableBranchWitnessToEventFlow (FableBranchWitnessUp.mk h m r E A H C P N)) m := by
    exact ⟨hsame_refl m, Exists.intro W rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro m sourceMark
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨hsame_refl m, rfl⟩
  }

theorem FableBranchWitnessCarrier_local_transport
    {h m r E A H C P N transportRead branchRead : BHist} :
    UnaryHistory h ->
      UnaryHistory E ->
        UnaryHistory H ->
          UnaryHistory C ->
            UnaryHistory N ->
              Cont h E r ->
                Cont H C transportRead ->
                  Cont transportRead N branchRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
                            hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row branchRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
                            Cont transportRead N branchRead)
                        hsame ∧
                      UnaryHistory r ∧ UnaryHistory transportRead ∧
                        UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: FableBranchWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro hUnary eUnary hTransportUnary cUnary nUnary emptyRoute transportRoute branchRoute
  have rUnary : UnaryHistory r :=
    unary_cont_closed hUnary eUnary emptyRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed hTransportUnary cUnary transportRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed transportUnary nUnary branchRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
              Cont transportRead N branchRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead ⟨hsame_refl branchRead, branchUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, emptyRoute, transportRoute, branchRoute⟩
  }
  exact ⟨cert, rUnary, transportUnary, branchUnary⟩

theorem FableBranchWitnessCarrier_scoped_dependency_package
    {h m r E A H C P N transportRead branchRead : BHist} :
    UnaryHistory h →
      UnaryHistory E →
        UnaryHistory H →
          UnaryHistory C →
            UnaryHistory N →
              Cont h E r →
                Cont H C transportRead →
                  Cont transportRead N branchRead →
                    SemanticNameCert
                        (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
                            hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                              hsame row N ∨ hsame row branchRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
                            Cont transportRead N branchRead)
                        hsame ∧
                      UnaryHistory r ∧ UnaryHistory transportRead ∧
                        UnaryHistory branchRead ∧
                          List.Mem (fableBranchWitnessEncodeBHist N)
                            (fableBranchWitnessToEventFlow
                              (FableBranchWitnessUp.mk h m r E A H C P N)) := by
  -- BEDC touchpoint anchor: FableBranchWitnessCarrier BHist BMark Cont hsame SemanticNameCert UnaryHistory
  intro hUnary eUnary hTransportUnary cUnary nUnary emptyRoute transportRoute branchRoute
  have localPackage :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
              Cont transportRead N branchRead)
          hsame ∧
        UnaryHistory r ∧ UnaryHistory transportRead ∧ UnaryHistory branchRead :=
    FableBranchWitnessCarrier_local_transport hUnary eUnary hTransportUnary cUnary nUnary
      emptyRoute transportRoute branchRoute
  have nameListed :
      List.Mem (fableBranchWitnessEncodeBHist N)
        (fableBranchWitnessToEventFlow
          (FableBranchWitnessUp.mk h m r E A H C P N)) := by
    change
      List.Mem (fableBranchWitnessEncodeBHist N)
        [[BMark.b0], fableBranchWitnessEncodeBHist h, [BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist m, [BMark.b1, BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist r, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist E,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          fableBranchWitnessEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          fableBranchWitnessEncodeBHist N]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
  exact
    ⟨localPackage.left, localPackage.right.left, localPackage.right.right.left,
      localPackage.right.right.right, nameListed⟩

theorem FableBranchWitnessCarrier_public_export
    {h m r E A H C P N transportRead branchRead exportRead : BHist} :
    UnaryHistory h -> UnaryHistory E -> UnaryHistory H -> UnaryHistory C -> UnaryHistory P ->
      UnaryHistory N -> Cont h E r -> Cont H C transportRead ->
        Cont transportRead N branchRead -> Cont branchRead P exportRead ->
          SemanticNameCert
              (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row branchRead ∨ hsame row exportRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
                  Cont transportRead N branchRead ∧ Cont branchRead P exportRead)
              hsame ∧
            UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: FableBranchWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro hUnary eUnary hTransportUnary cUnary pUnary nUnary emptyRoute transportRoute
    branchRoute exportRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed hTransportUnary cUnary transportRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed transportUnary nUnary branchRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed branchUnary pUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row branchRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h E r ∧ Cont H C transportRead ∧
              Cont transportRead N branchRead ∧ Cont branchRead P exportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, emptyRoute, transportRoute, branchRoute, exportRoute⟩
  }
  exact ⟨cert, exportUnary⟩

theorem FableBranchWitnessCarrier_formal_target_route
    {h m r E A H C P N admissibilityRead transportRead replayRead provenanceRead
      branchRead : BHist} :
    UnaryHistory h -> UnaryHistory E -> UnaryHistory A -> UnaryHistory H ->
      UnaryHistory C -> UnaryHistory P -> UnaryHistory N -> Cont h E r ->
        Cont r A admissibilityRead ->
          Cont admissibilityRead H transportRead ->
            Cont transportRead C replayRead ->
              Cont replayRead P provenanceRead ->
                Cont provenanceRead N branchRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
                          hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row admissibilityRead ∨
                              hsame row transportRead ∨ hsame row replayRead ∨
                                hsame row provenanceRead ∨ hsame row branchRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont h E r ∧ Cont r A admissibilityRead ∧
                          Cont admissibilityRead H transportRead ∧
                            Cont transportRead C replayRead ∧
                              Cont replayRead P provenanceRead ∧
                                Cont provenanceRead N branchRead)
                      hsame ∧ UnaryHistory branchRead := by
  -- BEDC touchpoint anchor: FableBranchWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro hUnary eUnary aUnary hTransportUnary cUnary pUnary nUnary emptyRoute
    admissibilityRoute transportRoute replayRoute provenanceRoute branchRoute
  have rUnary : UnaryHistory r :=
    unary_cont_closed hUnary eUnary emptyRoute
  have admissibilityUnary : UnaryHistory admissibilityRead :=
    unary_cont_closed rUnary aUnary admissibilityRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed admissibilityUnary hTransportUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed replayUnary pUnary provenanceRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed provenanceUnary nUnary branchRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row branchRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row admissibilityRead ∨
                  hsame row transportRead ∨ hsame row replayRead ∨
                    hsame row provenanceRead ∨ hsame row branchRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont h E r ∧ Cont r A admissibilityRead ∧
              Cont admissibilityRead H transportRead ∧ Cont transportRead C replayRead ∧
                Cont replayRead P provenanceRead ∧ Cont provenanceRead N branchRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro branchRead ⟨hsame_refl branchRead, branchUnary⟩
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
      right; right; right; right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, emptyRoute, admissibilityRoute, transportRoute, replayRoute,
          provenanceRoute, branchRoute⟩
  }
  exact ⟨cert, branchUnary⟩

end BEDC.Derived.FableBranchWitnessUp
