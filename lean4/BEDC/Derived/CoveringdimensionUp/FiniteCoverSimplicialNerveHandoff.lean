import BEDC.Derived.CoveringdimensionUp.FiniteCoverCarrier

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverSimplicialNerveHandoff [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead cover refinement orderBound nerve realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverCarrier compactMetric epsilonNet metricRead cover refinement
        orderBound nerve realSeal transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                hsame row nerve ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilonNet cover metricRead ∧
              Cont cover refinement orderBound ∧ Cont orderBound nerve realSeal ∧
                PkgSig bundle localName pkg)
          hsame ∧ UnaryHistory nerve ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteCoverCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro finiteCarrier
  obtain ⟨carrier, metricUnary, epsilonCoverMetric, coverRefinementOrder,
    orderNerveRealSeal, localPkg⟩ := finiteCarrier
  obtain ⟨_compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    realSealUnaryFromCarrier, _transportUnary, _replayUnary, _provenanceUnary, _localUnary,
    _compactEpsilonCover, _coverRefinementOrderFromCarrier, _orderRealReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have nerveUnary : UnaryHistory nerve :=
    unary_cont_right_factor orderNerveRealSeal realSealUnaryFromCarrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed orderUnary nerveUnary orderNerveRealSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                hsame row nerve ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilonNet cover metricRead ∧
              Cont cover refinement orderBound ∧ Cont orderBound nerve realSeal ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact ⟨source.right, epsilonCoverMetric, coverRefinementOrder, orderNerveRealSeal, localPkg⟩
  }
  exact ⟨cert, nerveUnary, realSealUnary⟩

end BEDC.Derived.CoveringdimensionUp
