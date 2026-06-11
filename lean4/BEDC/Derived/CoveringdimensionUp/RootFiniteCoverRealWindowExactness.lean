import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootFiniteCoverRealWindowExactness [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName realWindow ratWindow dyadicWindow completionWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      UnaryHistory realWindow →
        UnaryHistory dyadicWindow →
          Cont lebesgue realWindow ratWindow →
            Cont ratWindow dyadicWindow completionWindow →
              PkgSig bundle completionWindow pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row refinement ∨ hsame row lebesgue ∨
                        hsame row realWindow ∨ hsame row ratWindow ∨ hsame row dyadicWindow ∨
                          hsame row completionWindow ∨ hsame row localName)
                    (fun row : BHist => UnaryHistory row)
                    (fun _row : BHist =>
                      PkgSig bundle localName pkg ∨ PkgSig bundle completionWindow pkg)
                    hsame ∧
                  UnaryHistory completionWindow := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier realWindowUnary dyadicWindowUnary lebesgueRealRoute ratDyadicRoute completionPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, localNamePkg⟩ := carrier
  have ratWindowUnary : UnaryHistory ratWindow :=
    unary_cont_closed lebesgueUnary realWindowUnary lebesgueRealRoute
  have completionWindowUnary : UnaryHistory completionWindow :=
    unary_cont_closed ratWindowUnary dyadicWindowUnary ratDyadicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cover ∨ hsame row refinement ∨ hsame row lebesgue ∨
              hsame row realWindow ∨ hsame row ratWindow ∨ hsame row dyadicWindow ∨
                hsame row completionWindow ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle localName pkg ∨ PkgSig bundle completionWindow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cover (Or.inl (hsame_refl cover))
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
        | inl coverSource =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) coverSource)
        | inr rest =>
            cases rest with
            | inl refinementSource =>
                exact
                  Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) refinementSource))
            | inr rest =>
                cases rest with
                | inl lebesgueSource =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) lebesgueSource)))
                | inr rest =>
                    cases rest with
                    | inl realWindowSource =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) realWindowSource))))
                    | inr rest =>
                        cases rest with
                        | inl ratWindowSource =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          ratWindowSource)))))
                        | inr rest =>
                            cases rest with
                            | inl dyadicWindowSource =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                dyadicWindowSource))))))
                            | inr rest =>
                                cases rest with
                                | inl completionWindowSource =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      completionWindowSource)))))))
                                | inr localNameSource =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans (hsame_symm sameRows)
                                                      localNameSource)))))))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl coverSource =>
          exact unary_transport coverUnary (hsame_symm coverSource)
      | inr rest =>
          cases rest with
          | inl refinementSource =>
              exact unary_transport refinementUnary (hsame_symm refinementSource)
          | inr rest =>
              cases rest with
              | inl lebesgueSource =>
                  exact unary_transport lebesgueUnary (hsame_symm lebesgueSource)
              | inr rest =>
                  cases rest with
                  | inl realWindowSource =>
                      exact unary_transport realWindowUnary (hsame_symm realWindowSource)
                  | inr rest =>
                      cases rest with
                      | inl ratWindowSource =>
                          exact unary_transport ratWindowUnary (hsame_symm ratWindowSource)
                      | inr rest =>
                          cases rest with
                          | inl dyadicWindowSource =>
                              exact unary_transport dyadicWindowUnary (hsame_symm dyadicWindowSource)
                          | inr rest =>
                              cases rest with
                              | inl completionWindowSource =>
                                  exact
                                    unary_transport completionWindowUnary
                                      (hsame_symm completionWindowSource)
                              | inr localNameSource =>
                                  exact unary_transport localNameUnary (hsame_symm localNameSource)
    ledger_sound := by
      intro _row _source
      exact Or.inr completionPkg
  }
  exact ⟨cert, completionWindowUnary⟩

end BEDC.Derived.CoveringdimensionUp
