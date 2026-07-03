import BEDC.Derived.PhysicalLawBridgeUp.ObligationPackage

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem PhysicalLawBridgeFieldFaithfulObligation
    {law empirical bridge object fit failure transport replay provenance name nameRead
      obligationRead : BHist} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay provenance
        name →
      Cont replay provenance nameRead →
      hsame nameRead name →
      Cont transport replay obligationRead →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                  hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                    hsame row nameRead ∨ hsame row obligationRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row nameRead ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance nameRead ∧
              Cont transport replay obligationRead ∧ hsame nameRead name)
          hsame ∧
        UnaryHistory law ∧ UnaryHistory empirical ∧ UnaryHistory bridge ∧
          UnaryHistory object ∧ UnaryHistory fit ∧ UnaryHistory failure ∧
            UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
              UnaryHistory name ∧ UnaryHistory nameRead ∧ UnaryHistory obligationRead ∧
                Cont law empirical bridge ∧ Cont object fit failure ∧
                  Cont transport replay provenance ∧ Cont replay provenance nameRead ∧
                    Cont transport replay obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PhysicalLawBridgeCarrier
  intro carrier replayProvenanceName sameName transportReplayObligation
  obtain ⟨lawUnary, empiricalUnary, bridgeUnary, objectUnary, fitUnary, failureUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, lawEmpiricalBridge,
    objectFitFailure, transportReplayProvenance⟩ := carrier
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenanceName
  have obligationReadUnary : UnaryHistory obligationRead :=
    unary_cont_closed transportUnary replayUnary transportReplayObligation
  have lawSource :
      (fun row : BHist =>
        (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
            hsame row object ∨ hsame row fit ∨ hsame row failure ∨
              hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                hsame row nameRead ∨ hsame row obligationRead) ∧
          UnaryHistory row) law := by
    exact ⟨Or.inl (hsame_refl law), lawUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                  hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                    hsame row nameRead ∨ hsame row obligationRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row nameRead ∨ hsame row obligationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance nameRead ∧
              Cont transport replay obligationRead ∧ hsame nameRead name)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro law lawSource
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
                          | inr rest₆ =>
                              cases rest₆ with
                              | inl sameTransport =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr (Or.inl sameTransport))))))
                              | inr rest₇ =>
                                  cases rest₇ with
                                  | inl sameReplay =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr (Or.inl sameReplay)))))))
                                  | inr rest₈ =>
                                      cases rest₈ with
                                      | inl sameProvenance =>
                                          exact
                                            Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inl sameProvenance))))))))
                                      | inr rest₉ =>
                                          cases rest₉ with
                                          | inl sameNameRead =>
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
                                                                  (Or.inr
                                                                    (Or.inl sameNameRead))))))))))
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
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      sameObligationRead))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, replayProvenanceName, transportReplayObligation, sameName⟩
  }
  exact
    ⟨cert, lawUnary, empiricalUnary, bridgeUnary, objectUnary, fitUnary, failureUnary,
      transportUnary, replayUnary, provenanceUnary, nameUnary, nameReadUnary,
      obligationReadUnary, lawEmpiricalBridge, objectFitFailure, transportReplayProvenance,
      replayProvenanceName, transportReplayObligation⟩

theorem PhysicalLawBridgeScopedTasteGateRoute [AskSetup] [PackageSetup]
    {law empirical bridge object fit failure transport replay provenance name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay
        provenance name →
      Cont replay provenance scopedRead →
        hsame scopedRead name →
          PkgSig bundle scopedRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                      hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                        hsame row scopedRead) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                    hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                      hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                        hsame row name ∨ hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont replay provenance scopedRead ∧
                    hsame scopedRead name ∧ PkgSig bundle scopedRead pkg)
                hsame ∧
              Nonempty (ChapterTasteGate PhysicalLawBridgeUp) ∧
                Nonempty (FieldFaithful PhysicalLawBridgeUp) ∧
                  Nonempty (Nontrivial PhysicalLawBridgeUp) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier replayProvenance sameScoped scopedPkg
  obtain ⟨_lawUnary, _empiricalUnary, _bridgeUnary, _objectUnary, _fitUnary,
    _failureUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _lawEmpiricalBridge, _objectFitFailure, _transportReplayProvenance⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have scopedSource :
      (fun row : BHist =>
        (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨ hsame row object ∨
            hsame row fit ∨ hsame row failure ∨ hsame row scopedRead) ∧
          UnaryHistory row) scopedRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (hsame_refl scopedRead)))))),
        scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                  hsame row scopedRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance scopedRead ∧
              hsame scopedRead name ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead scopedSource
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
                          | inr sameScopedRead =>
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
                                                  (Or.inr sameScopedRead)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayProvenance, sameScoped, scopedPkg⟩
  }
  exact
    ⟨cert, ⟨physicalLawBridgeChapterTasteGate⟩,
      ⟨physicalLawBridgeFieldFaithful⟩, ⟨physicalLawBridgeNontrivial⟩⟩

theorem PhysicalLawBridgePublicClosureRoute [AskSetup] [PackageSetup]
    {law empirical bridge object fit failure transport replay provenance name scopedRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay
        provenance name →
      Cont replay provenance scopedRead →
        hsame scopedRead name →
          Cont scopedRead transport publicRead →
            PkgSig bundle scopedRead pkg →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                          hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                            hsame row scopedRead ∨ hsame row publicRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                        hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                          hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                            hsame row name ∨ hsame row scopedRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont replay provenance scopedRead ∧
                        hsame scopedRead name ∧ Cont scopedRead transport publicRead ∧
                          PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory scopedRead ∧ UnaryHistory publicRead ∧
                    Cont scopedRead transport publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier replayProvenance sameScoped scopedPublic _scopedPkg publicPkg
  obtain ⟨_lawUnary, _empiricalUnary, _bridgeUnary, _objectUnary, _fitUnary,
    _failureUnary, transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _lawEmpiricalBridge, _objectFitFailure, _transportReplayProvenance⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed scopedUnary transportUnary scopedPublic
  have publicSource :
      (fun row : BHist =>
        (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨ hsame row object ∨
            hsame row fit ∨ hsame row failure ∨ hsame row scopedRead ∨
              hsame row publicRead) ∧
          UnaryHistory row) publicRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (hsame_refl publicRead))))))),
        publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
                hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                  hsame row scopedRead ∨ hsame row publicRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row law ∨ hsame row empirical ∨ hsame row bridge ∨
              hsame row object ∨ hsame row fit ∨ hsame row failure ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row scopedRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replay provenance scopedRead ∧
              hsame scopedRead name ∧ Cont scopedRead transport publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead publicSource
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
                          | inr rest₆ =>
                              cases rest₆ with
                              | inl sameScopedRead =>
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
                                                      (Or.inr
                                                        (Or.inl sameScopedRead))))))))))
                              | inr samePublicRead =>
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
                                                      (Or.inr
                                                        (Or.inr samePublicRead))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayProvenance, sameScoped, scopedPublic, publicPkg⟩
  }
  exact ⟨cert, scopedUnary, publicUnary, scopedPublic⟩

end BEDC.Derived.PhysicalLawBridgeUp
