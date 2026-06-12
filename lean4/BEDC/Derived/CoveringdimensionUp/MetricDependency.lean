import BEDC.Derived.CoveringdimensionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionMetricDependency [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead coverRead dimensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead cover coverRead →
          Cont coverRead orderBound dimensionRead →
            PkgSig bundle dimensionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row dimensionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row orderBound ∨ hsame row metricRead ∨ hsame row coverRead ∨
                        hsame row dimensionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                      Cont metricRead cover coverRead ∧
                        Cont coverRead orderBound dimensionRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle dimensionRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory dimensionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute coverRoute dimensionRoute dimensionPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed metricUnary coverUnary coverRoute
  have dimensionUnary : UnaryHistory dimensionRead :=
    unary_cont_closed coverReadUnary orderUnary dimensionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dimensionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row orderBound ∨ hsame row metricRead ∨ hsame row coverRead ∨
                hsame row dimensionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead cover coverRead ∧ Cont coverRead orderBound dimensionRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle dimensionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dimensionRead ⟨hsame_refl dimensionRead, dimensionUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricRoute, coverRoute, dimensionRoute, provenancePkg,
          dimensionPkg⟩
  }
  exact ⟨cert, metricUnary, coverReadUnary, dimensionUnary⟩

end BEDC.Derived.CoveringdimensionUp
