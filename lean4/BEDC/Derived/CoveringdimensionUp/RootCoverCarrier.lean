import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverCarrier [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                  hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                    hsame row rootRead ∨ hsame row localName)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier coverRefinementRoot rootPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRoot
  constructor
  · exact {
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
                              | inr rest =>
                                  cases rest with
                                  | inl rootSource =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm sameRows)
                                                        rootSource)))))))
                                  | inr localSource =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (hsame_trans (hsame_symm sameRows)
                                                        localSource)))))))
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
                            | inr rest =>
                                cases rest with
                                | inl rootSource =>
                                    exact unary_transport rootUnary (hsame_symm rootSource)
                                | inr localSource =>
                                    exact unary_transport localNameUnary (hsame_symm localSource)
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, localNamePkg, rootPkg⟩
    }
  · exact rootUnary

end BEDC.Derived.CoveringdimensionUp
