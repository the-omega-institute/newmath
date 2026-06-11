import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionCompactNetOrderCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet metricRead refinement orderBound nerve transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory metricRead ∧
    UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory nerve ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont compactMetric epsilonNet metricRead ∧
          Cont metricRead refinement orderBound ∧ Cont orderBound nerve replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CoveringDimensionCompactNetOrderCarrier_admission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead refinement orderBound nerve transport replay provenance
      localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCompactNetOrderCarrier compactMetric epsilonNet metricRead refinement
        orderBound nerve transport replay provenance localName bundle pkg ->
      Cont replay localName consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                  hsame row refinement ∨ hsame row orderBound ∨ hsame row nerve ∨
                    hsame row replay ∨ hsame row consumer)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                  Cont metricRead refinement orderBound ∧ Cont orderBound nerve replay ∧
                    Cont replay localName consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier replayLocalNameConsumer consumerPkg
  obtain ⟨compactUnary, epsilonUnary, metricReadUnary, refinementUnary, orderUnary,
    nerveUnary, _transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    compactMetricRead, metricRefinementOrder, orderNerveReplay, provenancePkg,
    _localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary localNameUnary replayLocalNameConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row nerve ∨
                hsame row replay ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead refinement orderBound ∧ Cont orderBound nerve replay ∧
                Cont replay localName consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        ⟨source.right, compactMetricRead, metricRefinementOrder, orderNerveReplay,
          replayLocalNameConsumer, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.CoveringdimensionUp
