import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootMetricRealWindow [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead realWindow nerveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric cover metricRead →
        Cont metricRead lebesgue realWindow →
          Cont realWindow orderBound nerveRead →
            PkgSig bundle nerveRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row nerveRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨ hsame row metricRead ∨
                        hsame row realWindow ∨ hsame row nerveRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric cover metricRead ∧
                      Cont metricRead lebesgue realWindow ∧
                        Cont realWindow orderBound nerveRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle nerveRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory realWindow ∧
                  UnaryHistory nerveRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactCoverMetric metricLebesgueReal realOrderNerve nervePkg
  obtain ⟨compactUnary, _epsilonUnary, coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary coverUnary compactCoverMetric
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed metricReadUnary lebesgueUnary metricLebesgueReal
  have nerveReadUnary : UnaryHistory nerveRead :=
    unary_cont_closed realWindowUnary orderUnary realOrderNerve
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nerveRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row metricRead ∨
                hsame row realWindow ∨ hsame row nerveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric cover metricRead ∧
              Cont metricRead lebesgue realWindow ∧ Cont realWindow orderBound nerveRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle nerveRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nerveRead ⟨hsame_refl nerveRead, nerveReadUnary⟩
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
      exact
        ⟨source.right, compactCoverMetric, metricLebesgueReal, realOrderNerve,
          provenancePkg, nervePkg⟩
  }
  exact ⟨cert, metricReadUnary, realWindowUnary, nerveReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
