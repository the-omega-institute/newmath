import BEDC.Derived.PhysicalLawBridgeUp.NameCertSurface
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PhysicalLawBridgeObligationPackage
    {law empirical bridge object fit failure transport replay provenance name obligationRead : BHist} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay provenance name →
      Cont replay provenance obligationRead →
        hsame obligationRead name →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                    hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                      hsame row obligationRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                  hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                    hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row name ∨ hsame row obligationRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont replay provenance obligationRead ∧
                  hsame obligationRead name)
              hsame ∧
            UnaryHistory obligationRead ∧ hsame obligationRead name := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PhysicalLawBridgeCarrier
  intro carrier replayProvenance sameObligation
  obtain ⟨lawUnary, empiricalUnary, bridgeUnary, objectUnary, fitUnary, failureUnary,
    _transportUnary, replayUnary, provenanceUnary, _nameUnary, _lawEmpiricalBridge,
    _objectFitFailure, _transportReplayProvenance⟩ := carrier
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have obligationSource :
      (fun row : BHist =>
        (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨ hsame row object ∨
            hsame row fit ∨ hsame row failure ∨ hsame row obligationRead) ∧
          UnaryHistory row) obligationRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl obligationRead)))))),
        obligationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                  hsame row obligationRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance obligationRead ∧
              hsame obligationRead name)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead obligationSource
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
        have transportedUnary : UnaryHistory _ :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameLaw =>
            exact ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameLaw), transportedUnary⟩
        | inr rest₁ =>
            cases rest₁ with
            | inl sameEmpirical =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEmpirical)),
                    transportedUnary⟩
            | inr rest₂ =>
                cases rest₂ with
                | inl sameBridge =>
                    exact
                      ⟨Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBridge))),
                        transportedUnary⟩
                | inr rest₃ =>
                    cases rest₃ with
                    | inl sameObject =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) sameObject)))),
                            transportedUnary⟩
                    | inr rest₄ =>
                        cases rest₄ with
                        | inl sameFit =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameFit))))),
                                transportedUnary⟩
                        | inr rest₅ =>
                            cases rest₅ with
                            | inl sameFailure =>
                                exact
                                  ⟨Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameFailure)))))),
                                    transportedUnary⟩
                            | inr sameObligationRead =>
                                exact
                                  ⟨Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameObligationRead)))))),
                                    transportedUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLaw =>
          exact Or.inl sameLaw
      | inr rest₁ =>
          cases rest₁ with
          | inl sameEmpirical =>
              exact Or.inr (Or.inl sameEmpirical)
          | inr rest₂ =>
              cases rest₂ with
              | inl sameBridge =>
                  exact Or.inr (Or.inr (Or.inl sameBridge))
              | inr rest₃ =>
                  cases rest₃ with
                  | inl sameObject =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameObject)))
                  | inr rest₄ =>
                      cases rest₄ with
                      | inl sameFit =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFit))))
                      | inr rest₅ =>
                          cases rest₅ with
                          | inl sameFailure =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr (Or.inr (Or.inl sameFailure)))))
                          | inr sameObligationRead =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr sameObligationRead)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayProvenance, sameObligation⟩
  }
  exact ⟨cert, obligationUnary, sameObligation⟩

end BEDC.Derived.PhysicalLawBridgeUp
