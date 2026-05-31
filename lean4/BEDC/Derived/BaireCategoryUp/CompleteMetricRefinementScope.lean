import BEDC.Derived.BaireCategoryUp.NameCertObligations

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_complete_metric_refinement_scope [AskSetup] [PackageSetup]
    {B M D O R T H C P N refinementRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg ->
      Cont D O R ->
        Cont R T refinementRead ->
          Cont refinementRead M terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row refinementRead ∨ hsame row terminalRead ∨ hsame row M)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨ hsame row M ∨
                      hsame row refinementRead ∨ hsame row terminalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
                      Cont refinementRead M terminalRead)
                  hsame ∧
                UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory R ∧ UnaryHistory T ∧
                  UnaryHistory M ∧ UnaryHistory refinementRead ∧ UnaryHistory terminalRead ∧
                    Cont D O R ∧ Cont R T refinementRead ∧
                      Cont refinementRead M terminalRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseOpenRoute refinementRoute terminalRoute terminalPkg
  obtain ⟨_prefixUnary, metricUnary, denseUnary, openUnary, refinementUnary, threadUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed refinementUnary threadUnary refinementRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed refinementReadUnary metricUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refinementRead ∨ hsame row terminalRead ∨ hsame row M)
          (fun row : BHist =>
            hsame row D ∨ hsame row O ∨ hsame row R ∨ hsame row T ∨ hsame row M ∨
              hsame row refinementRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg ∧
              Cont refinementRead M terminalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refinementRead (Or.inl (hsame_refl refinementRead))
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
        | inl sameRefinement =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRefinement)
        | inr rest =>
            cases rest with
            | inl sameTerminal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal))
            | inr sameMetric =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameMetric))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameRefinement =>
          exact Or.inr
            (Or.inr
              (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inl sameRefinement)))))
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sameTerminal)))))
          | inr sameMetric =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inl sameMetric))))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameRefinement =>
          exact
            ⟨unary_transport refinementReadUnary (hsame_symm sameRefinement), provenancePkg,
              terminalPkg, terminalRoute⟩
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact
                ⟨unary_transport terminalReadUnary (hsame_symm sameTerminal), provenancePkg,
                  terminalPkg, terminalRoute⟩
          | inr sameMetric =>
              exact
                ⟨unary_transport metricUnary (hsame_symm sameMetric), provenancePkg, terminalPkg,
                  terminalRoute⟩
  }
  exact
    ⟨cert, denseUnary, openUnary, refinementUnary, threadUnary, metricUnary, refinementReadUnary,
      terminalReadUnary, denseOpenRoute, refinementRoute, terminalRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.BaireCategoryUp
