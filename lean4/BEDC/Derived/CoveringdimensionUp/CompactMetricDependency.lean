import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCompactMetricDependency [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead cover dependencyRead →
          PkgSig bundle dependencyRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                    hsame row cover ∨ hsame row dependencyRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                    hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                      hsame row dependencyRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle dependencyRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory dependencyRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier metricRoute dependencyRoute dependencyPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    _lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed metricUnary coverUnary dependencyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row dependencyRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                hsame row dependencyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle dependencyRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl dependencyRead)))),
            dependencyUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompact =>
          exact Or.inl sameCompact
      | inr rest =>
          cases rest with
          | inl sameEpsilon =>
              exact Or.inr (Or.inl sameEpsilon)
          | inr rest =>
              cases rest with
              | inl sameMetric =>
                  exact Or.inr (Or.inr (Or.inl sameMetric))
              | inr rest =>
                  cases rest with
                  | inl sameCover =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameCover)))
                  | inr sameDependency =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr sameDependency)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, dependencyPkg, provenancePkg⟩
  }
  exact ⟨cert, metricUnary, dependencyUnary⟩

end BEDC.Derived.CoveringdimensionUp
