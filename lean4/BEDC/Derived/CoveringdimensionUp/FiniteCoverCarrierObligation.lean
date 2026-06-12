import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverCarrierObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName carrierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet carrierRead →
        PkgSig bundle carrierRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                  hsame row refinement ∨ hsame row orderBound ∨ hsame row localName ∨
                    hsame row carrierRead)
              (fun row : BHist => UnaryHistory row)
              (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle carrierRead pkg)
              hsame ∧
            UnaryHistory carrierRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactEpsilonCarrierRead carrierReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have carrierReadUnary : UnaryHistory carrierRead :=
    unary_cont_closed compactUnary epsilonUnary compactEpsilonCarrierRead
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
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) epsilonSource))
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
                              | inl localNameSource =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  localNameSource))))))
                              | inr carrierReadSource =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (hsame_trans (hsame_symm sameRows)
                                                  carrierReadSource))))))
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
                            | inl localNameSource =>
                                exact unary_transport localNameUnary (hsame_symm localNameSource)
                            | inr carrierReadSource =>
                                exact unary_transport carrierReadUnary (hsame_symm carrierReadSource)
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, carrierReadPkg⟩
    }
  · exact carrierReadUnary

end BEDC.Derived.CoveringdimensionUp
