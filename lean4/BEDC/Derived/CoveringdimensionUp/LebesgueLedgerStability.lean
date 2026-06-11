import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionLebesgueLedgerStability [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName ledgerRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg ->
      Cont orderBound lebesgue ledgerRead ->
        Cont ledgerRead transport stableRead ->
          PkgSig bundle stableRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                      hsame row ledgerRead ∨ hsame row stableRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont orderBound lebesgue ledgerRead ∧
                    Cont ledgerRead transport stableRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle stableRead pkg)
                hsame ∧
              UnaryHistory ledgerRead ∧ UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ledgerRoute stableRoute stablePkg
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed orderUnary lebesgueUnary ledgerRoute
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed ledgerUnary transportUnary stableRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row ledgerRead ∨ hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont orderBound lebesgue ledgerRead ∧
              Cont ledgerRead transport stableRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle stableRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRoute, stableRoute, provenancePkg, stablePkg⟩
  }
  exact ⟨cert, ledgerUnary, stableUnary⟩

end BEDC.Derived.CoveringdimensionUp
