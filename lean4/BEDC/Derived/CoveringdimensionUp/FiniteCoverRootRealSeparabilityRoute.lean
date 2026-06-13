import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverRootRealSeparabilityRoute [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName metricRead densityRead separabilityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet metricRead →
        Cont metricRead lebesgue densityRead →
          Cont densityRead orderBound separabilityRead →
            PkgSig bundle separabilityRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row separabilityRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                      hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                        hsame row metricRead ∨ hsame row densityRead ∨
                          hsame row separabilityRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                      Cont metricRead lebesgue densityRead ∧
                        Cont densityRead orderBound separabilityRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle separabilityRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory densityRead ∧
                  UnaryHistory separabilityRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute densityRoute separabilityRoute separabilityPkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, _refinementUnary, orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, provenanceUnary, _localNameUnary,
      _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
        _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary epsilonUnary metricRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed metricUnary lebesgueUnary densityRoute
  have separabilityUnary : UnaryHistory separabilityRead :=
    unary_cont_closed densityUnary orderUnary separabilityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separabilityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                hsame row metricRead ∨ hsame row densityRead ∨
                  hsame row separabilityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead lebesgue densityRead ∧
                Cont densityRead orderBound separabilityRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle separabilityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separabilityRead ⟨hsame_refl separabilityRead, separabilityUnary⟩
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
        ⟨source.right, metricRoute, densityRoute, separabilityRoute, provenancePkg,
          separabilityPkg⟩
  }
  exact ⟨cert, metricUnary, densityUnary, separabilityUnary⟩

end BEDC.Derived.CoveringdimensionUp
