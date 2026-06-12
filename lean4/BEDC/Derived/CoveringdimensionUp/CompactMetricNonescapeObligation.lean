import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactMetricNonescapeObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName netRead coverRead finiteRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet netRead →
        Cont netRead cover coverRead →
          Cont coverRead refinement finiteRead →
            PkgSig bundle finiteRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨ hsame row finiteRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet netRead ∧
                      Cont netRead cover coverRead ∧
                        Cont coverRead refinement finiteRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle finiteRead pkg)
                  hsame ∧
                UnaryHistory netRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory finiteRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactNetRoute netCoverRoute coverRefinementRoute finitePkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have netReadUnary : UnaryHistory netRead :=
    unary_cont_closed compactUnary epsilonUnary compactNetRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed netReadUnary coverUnary netCoverRoute
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed coverReadUnary refinementUnary coverRefinementRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row finiteRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet netRead ∧
              Cont netRead cover coverRead ∧ Cont coverRead refinement finiteRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle finiteRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finiteRead ⟨hsame_refl finiteRead, finiteReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactNetRoute, netCoverRoute, coverRefinementRoute,
          provenancePkg, finitePkg⟩
  }
  exact ⟨cert, netReadUnary, coverReadUnary, finiteReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
