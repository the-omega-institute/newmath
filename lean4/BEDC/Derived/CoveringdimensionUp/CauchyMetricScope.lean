import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCauchyMetricScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound realSeal transport replay provenance
      localName metricRead realWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound realSeal
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead realSeal realWindow →
          PkgSig bundle realWindow pkg →
            SemanticNameCert
                (fun row : BHist => hsame row realWindow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                    hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                      hsame row realSeal ∨ hsame row realWindow)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                    Cont metricRead realSeal realWindow ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realWindow pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory realWindow := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute realRoute realPkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderRealReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed metricReadUnary realSealUnary realRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro realWindow ⟨hsame_refl realWindow, realWindowUnary⟩
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
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, metricRoute, realRoute, provenancePkg, realPkg⟩
    }
  · exact ⟨metricReadUnary, realWindowUnary⟩

end BEDC.Derived.CoveringdimensionUp
