import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactCoverForwardDependency [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactCoverRead compactCoverLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont cover refinement compactCoverRead →
        Cont compactCoverRead lebesgue compactCoverLedger →
          PkgSig bundle compactCoverLedger pkg →
            SemanticNameCert
                (fun row : BHist => hsame row compactCoverLedger ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row refinement ∨ hsame row lebesgue ∨
                    hsame row compactCoverRead ∨ hsame row compactCoverLedger)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont cover refinement compactCoverRead ∧
                    Cont compactCoverRead lebesgue compactCoverLedger ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle compactCoverLedger pkg)
                hsame ∧
              UnaryHistory compactCoverRead ∧ UnaryHistory compactCoverLedger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier coverRefinementRead readLebesgueLedger compactCoverLedgerPkg
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactCoverReadUnary : UnaryHistory compactCoverRead :=
    unary_cont_closed coverUnary refinementUnary coverRefinementRead
  have compactCoverLedgerUnary : UnaryHistory compactCoverLedger :=
    unary_cont_closed compactCoverReadUnary lebesgueUnary readLebesgueLedger
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactCoverLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row refinement ∨ hsame row lebesgue ∨
              hsame row compactCoverRead ∨ hsame row compactCoverLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cover refinement compactCoverRead ∧
              Cont compactCoverRead lebesgue compactCoverLedger ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle compactCoverLedger pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactCoverLedger ⟨hsame_refl compactCoverLedger,
          compactCoverLedgerUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRefinementRead, readLebesgueLedger, provenancePkg,
          compactCoverLedgerPkg⟩
  }
  exact ⟨cert, compactCoverReadUnary, compactCoverLedgerUnary⟩

end BEDC.Derived.CoveringdimensionUp
