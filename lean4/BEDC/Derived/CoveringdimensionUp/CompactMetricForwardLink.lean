import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactMetricForwardLink [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead finiteCoverRead dimensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead cover finiteCoverRead →
          Cont finiteCoverRead orderBound dimensionRead →
            PkgSig bundle dimensionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row dimensionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨
                      hsame row metricRead ∨ hsame row cover ∨ hsame row finiteCoverRead ∨
                        hsame row refinement ∨ hsame row orderBound ∨
                          hsame row lebesgue ∨ hsame row dimensionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                      Cont metricRead cover finiteCoverRead ∧
                        Cont finiteCoverRead orderBound dimensionRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle dimensionRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory finiteCoverRead ∧
                  UnaryHistory dimensionRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute coverRoute dimensionRoute dimensionPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have finiteCoverReadUnary : UnaryHistory finiteCoverRead :=
    unary_cont_closed metricReadUnary coverUnary coverRoute
  have dimensionReadUnary : UnaryHistory dimensionRead :=
    unary_cont_closed finiteCoverReadUnary orderUnary dimensionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dimensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row finiteCoverRead ∨ hsame row refinement ∨
                hsame row orderBound ∨ hsame row lebesgue ∨ hsame row dimensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead cover finiteCoverRead ∧
                Cont finiteCoverRead orderBound dimensionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle dimensionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dimensionRead ⟨hsame_refl dimensionRead, dimensionReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricRoute, coverRoute, dimensionRoute, provenancePkg,
          dimensionPkg⟩
  }
  exact ⟨cert, metricReadUnary, finiteCoverReadUnary, dimensionReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
