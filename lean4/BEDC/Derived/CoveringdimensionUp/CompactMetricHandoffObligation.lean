import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactMetricHandoffObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont lebesgue replay handoffRead →
        PkgSig bundle handoffRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                  hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                    hsame row handoffRead)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
              hsame ∧
            UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier lebesgueReplayHandoff handoffPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed lebesgueUnary replayUnary lebesgueReplayHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row handoffRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactMetric (Or.inl (hsame_refl compactMetric))
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
        cases source with
        | inl compactSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) compactSource)
        | inr rest =>
            cases rest with
            | inl epsilonSource =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) epsilonSource))
            | inr rest =>
                cases rest with
                | inl coverSource =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) coverSource)))
                | inr rest =>
                    cases rest with
                    | inl refinementSource =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) refinementSource))))
                    | inr rest =>
                        cases rest with
                        | inl orderSource =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) orderSource)))))
                        | inr rest =>
                            cases rest with
                            | inl lebesgueSource =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                lebesgueSource))))))
                            | inr handoffSource =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (hsame_trans (hsame_symm sameRows)
                                                handoffSource))))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl compactSource =>
          exact unary_transport compactUnary (hsame_symm compactSource)
      | inr rest =>
          cases rest with
          | inl epsilonSource =>
              exact unary_transport epsilonUnary (hsame_symm epsilonSource)
          | inr rest =>
              cases rest with
              | inl coverSource =>
                  exact unary_transport coverUnary (hsame_symm coverSource)
              | inr rest =>
                  cases rest with
                  | inl refinementSource =>
                      exact unary_transport refinementUnary (hsame_symm refinementSource)
                  | inr rest =>
                      cases rest with
                      | inl orderSource =>
                          exact unary_transport orderUnary (hsame_symm orderSource)
                      | inr rest =>
                          cases rest with
                          | inl lebesgueSource =>
                              exact unary_transport lebesgueUnary (hsame_symm lebesgueSource)
                          | inr handoffSource =>
                              exact unary_transport handoffUnary (hsame_symm handoffSource)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, handoffUnary⟩

end BEDC.Derived.CoveringdimensionUp
