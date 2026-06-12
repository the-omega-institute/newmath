import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionLebesgueLedgerHandoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName lebesgueRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont orderBound lebesgue lebesgueRead →
        Cont lebesgueRead replay namedRead →
          PkgSig bundle namedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                    hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgueRead ∨
                      hsame row namedRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
                hsame ∧
              UnaryHistory lebesgueRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier lebesgueRoute namedRoute namedPkg
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have lebesgueReadUnary : UnaryHistory lebesgueRead :=
    unary_cont_closed orderUnary lebesgueUnary lebesgueRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed lebesgueReadUnary replayUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgueRead ∨
                hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namedPkg⟩
  }
  exact ⟨cert, lebesgueReadUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
