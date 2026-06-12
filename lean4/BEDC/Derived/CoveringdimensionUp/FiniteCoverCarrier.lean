import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteCoverCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet metricRead cover refinement orderBound nerve realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound realSeal transport
      replay provenance localName bundle pkg ∧
    UnaryHistory metricRead ∧ Cont epsilonNet cover metricRead ∧
      Cont cover refinement orderBound ∧ Cont orderBound nerve realSeal ∧
        PkgSig bundle localName pkg

theorem CoveringDimensionFiniteCoverCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead cover refinement orderBound nerve realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverCarrier compactMetric epsilonNet metricRead cover refinement
        orderBound nerve realSeal transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                hsame row nerve ∨ hsame row realSeal ∨ hsame row transport ∨
                  hsame row replay ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilonNet cover metricRead ∧
              Cont cover refinement orderBound ∧ Cont orderBound nerve realSeal ∧
                PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteCoverCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro finiteCarrier
  obtain ⟨carrier, metricUnary, epsilonCoverMetric, coverRefinementOrder,
    orderNerveRealSeal, localPkg⟩ := finiteCarrier
  obtain ⟨_compactUnary, _epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    _realUnary, _transportUnary, _replayUnary, _provenanceUnary, localUnary,
    _compactEpsilonCover, _coverRefinementOrderFromCarrier, _orderRealReplay,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory localName := localUnary
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨hsame_refl localName, sourceUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, epsilonCoverMetric, coverRefinementOrder, orderNerveRealSeal, localPkg⟩
  }

end BEDC.Derived.CoveringdimensionUp
