import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverObligations [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName finiteCoverRead supportRead orderExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet finiteCoverRead →
        Cont finiteCoverRead cover supportRead →
          Cont supportRead orderBound orderExport →
            PkgSig bundle orderExport pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row orderExport ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                        hsame row finiteCoverRead ∨ hsame row supportRead ∨
                          hsame row orderExport ∨ hsame row localName)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet finiteCoverRead ∧
                      Cont finiteCoverRead cover supportRead ∧
                        Cont supportRead orderBound orderExport ∧
                          PkgSig bundle orderExport pkg)
                  hsame ∧ UnaryHistory finiteCoverRead ∧ UnaryHistory supportRead ∧
                UnaryHistory orderExport := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier finiteCoverRoute supportRoute orderRoute orderPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have finiteCoverUnary : UnaryHistory finiteCoverRead :=
    unary_cont_closed compactUnary epsilonUnary finiteCoverRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed finiteCoverUnary coverUnary supportRoute
  have orderExportUnary : UnaryHistory orderExport :=
    unary_cont_closed supportUnary orderUnary orderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row finiteCoverRead ∨ hsame row supportRead ∨
                  hsame row orderExport ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet finiteCoverRead ∧
              Cont finiteCoverRead cover supportRead ∧ Cont supportRead orderBound orderExport ∧
                PkgSig bundle orderExport pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro orderExport ⟨hsame_refl orderExport, orderExportUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sourceData.left))))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, finiteCoverRoute, supportRoute, orderRoute, orderPkg⟩
  }
  exact ⟨cert, finiteCoverUnary, supportUnary, orderExportUnary⟩

end BEDC.Derived.CoveringdimensionUp
