import BEDC.Derived.CoveringdimensionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringDimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CoveringdimensionUp

theorem CoveringDimensionRealSeparabilityRouteScope [AskSetup] [PackageSetup]
    {compact metric epsilonNet regseq realSep cover refinement order lebesgue transport replay
      provenance localName routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compact epsilonNet cover refinement order lebesgue transport replay
        provenance localName bundle pkg →
      Cont realSep metric compact →
        Cont compact epsilonNet regseq →
          Cont regseq cover routeRead →
            PkgSig bundle routeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row realSep ∨ hsame row metric ∨ hsame row compact ∨
                      hsame row epsilonNet ∨ hsame row regseq ∨ hsame row cover ∨
                        hsame row routeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
                      PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier _realSepMetricCompact compactEpsilonRegseq regseqCoverRoute routePkg
  obtain ⟨_compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have regseqUnary : UnaryHistory regseq :=
    unary_cont_closed _compactUnary epsilonUnary compactEpsilonRegseq
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed regseqUnary coverUnary regseqCoverRoute
  have sourceRoute :
      (fun row : BHist => hsame row routeRead ∧ UnaryHistory row) routeRead := by
    exact ⟨hsame_refl routeRead, routeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row realSep ∨ hsame row metric ∨ hsame row compact ∨
              hsame row epsilonNet ∨ hsame row regseq ∨ hsame row cover ∨
                hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceRoute
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
      exact ⟨source.right, routePkg, provenancePkg⟩
  }
  exact ⟨cert, routeUnary⟩

end BEDC.Derived.CoveringDimensionUp
