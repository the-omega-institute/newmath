import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityMetricCompletionCoverRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName densityWindow completionBoundary coverOrderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont epsilonNet cover densityWindow →
        Cont densityWindow localName completionBoundary →
          Cont completionBoundary orderBound coverOrderRead →
            PkgSig bundle coverOrderRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row coverOrderRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row densityWindow ∨ hsame row completionBoundary ∨
                        hsame row orderBound ∨ hsame row coverOrderRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
                      Cont epsilonNet cover densityWindow ∧
                        Cont densityWindow localName completionBoundary ∧
                          Cont completionBoundary orderBound coverOrderRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle coverOrderRead pkg)
                  hsame ∧
                UnaryHistory densityWindow ∧ UnaryHistory completionBoundary ∧
                  UnaryHistory coverOrderRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier epsilonCoverDensity densityLocalCompletion completionOrderRead orderReadPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityWindow :=
    unary_cont_closed epsilonUnary coverUnary epsilonCoverDensity
  have completionUnary : UnaryHistory completionBoundary :=
    unary_cont_closed densityUnary localNameUnary densityLocalCompletion
  have coverOrderUnary : UnaryHistory coverOrderRead :=
    unary_cont_closed completionUnary orderUnary completionOrderRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverOrderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row densityWindow ∨ hsame row completionBoundary ∨ hsame row orderBound ∨
                hsame row coverOrderRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet cover ∧
              Cont epsilonNet cover densityWindow ∧
                Cont densityWindow localName completionBoundary ∧
                  Cont completionBoundary orderBound coverOrderRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle coverOrderRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro coverOrderRead ⟨hsame_refl coverOrderRead, coverOrderUnary⟩
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
      exact
        ⟨source.right, compactEpsilonCover, epsilonCoverDensity, densityLocalCompletion,
          completionOrderRead, provenancePkg, orderReadPkg⟩
  }
  exact ⟨cert, densityUnary, completionUnary, coverOrderUnary⟩

end BEDC.Derived.CoveringdimensionUp
