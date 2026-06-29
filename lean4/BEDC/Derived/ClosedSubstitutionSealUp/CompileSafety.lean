import BEDC.Derived.ClosedSubstitutionSealUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedSubstitutionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ClosedSubstitutionSeal_compile_safety (x : ClosedSubstitutionSealUp) :
    exists term depth payload closedness substitution shift audit handoff transport continuation
      provenance name : BHist,
      x = ClosedSubstitutionSealUp.mk term depth payload closedness substitution shift audit handoff
        transport continuation provenance name ∧
        closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) = some x ∧
          SemanticNameCert
            (fun row : BHist =>
              hsame row handoff ∨ hsame row transport ∨ hsame row continuation ∨
                hsame row provenance ∨ hsame row name)
            (fun row : BHist =>
              hsame row term ∨ hsame row depth ∨ hsame row payload ∨
                hsame row closedness ∨ hsame row substitution ∨ hsame row shift ∨
                  hsame row audit ∨ hsame row handoff ∨ hsame row transport ∨
                    hsame row continuation ∨ hsame row provenance ∨ hsame row name)
            (fun row : BHist =>
              hsame row closedness ∨ hsame row substitution ∨ hsame row shift ∨
                hsame row audit ∨ hsame row handoff ∨ hsame row transport ∨
                  hsame row continuation ∨ hsame row provenance ∨ hsame row name)
            hsame := by
  -- BEDC touchpoint anchor: ClosedSubstitutionSealUp BHist hsame SemanticNameCert NameCert
  cases x with
  | mk term depth payload closedness substitution shift audit handoff transport continuation
      provenance name =>
      refine ⟨term, depth, payload, closedness, substitution, shift, audit, handoff,
        transport, continuation, provenance, name, rfl, ?_, ?_⟩
      · exact
          (ClosedSubstitutionSealTasteGate_single_carrier_alignment.right.left
            (ClosedSubstitutionSealUp.mk term depth payload closedness substitution shift audit
              handoff transport continuation provenance name))
      · exact {
          core := {
            carrier_inhabited := Exists.intro name
              (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl name)))))
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
              intro row other sameRows source
              cases source with
              | inl sameHandoff =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff)
              | inr rest =>
                  cases rest with
                  | inl sameTransport =>
                      exact Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameTransport))
                  | inr rest =>
                      cases rest with
                      | inl sameContinuation =>
                          exact Or.inr
                            (Or.inr
                              (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameContinuation)))
                      | inr rest =>
                          cases rest with
                          | inl sameProvenance =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameProvenance))))
                          | inr sameName =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (hsame_trans (hsame_symm sameRows) sameName))))
          }
          pattern_sound := by
            intro _row source
            cases source with
            | inl sameHandoff =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl sameHandoff)))))))
            | inr rest =>
                cases rest with
                | inl sameTransport =>
                    exact Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl sameTransport))))))))
                | inr rest =>
                    cases rest with
                    | inl sameContinuation =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl sameContinuation)))))))))
                    | inr rest =>
                        cases rest with
                        | inl sameProvenance =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inl sameProvenance))))))))))
                        | inr sameName =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr sameName))))))))))
          ledger_sound := by
            intro _row source
            cases source with
            | inl sameHandoff =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sameHandoff))))
            | inr rest =>
                cases rest with
                | inl sameTransport =>
                    exact Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inl sameTransport)))))
                | inr rest =>
                    cases rest with
                    | inl sameContinuation =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl sameContinuation))))))
                    | inr rest =>
                        cases rest with
                        | inl sameProvenance =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl sameProvenance)))))))
                        | inr sameName =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr sameName)))))))
        }

end BEDC.Derived.ClosedSubstitutionSealUp
