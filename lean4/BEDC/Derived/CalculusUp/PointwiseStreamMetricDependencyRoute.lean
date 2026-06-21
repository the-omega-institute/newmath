import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusPointwiseStreamMetricDependencyRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      derivativeRead integralRead pointwiseMetricRead metricBoundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead pointwiseMetricRead →
            Cont pointwiseMetricRead real metricBoundRead →
              PkgSig bundle metricBoundRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row metricBoundRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row derivativeRead ∨ hsame row integralRead ∨
                        hsame row pointwiseMetricRead ∨ hsame row metricBoundRead ∨
                          hsame row real)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont derivativeRead integralRead pointwiseMetricRead ∧
                        Cont pointwiseMetricRead real metricBoundRead ∧
                          PkgSig bundle metricBoundRead pkg)
                    hsame ∧
                  UnaryHistory pointwiseMetricRead ∧ UnaryHistory metricBoundRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier derivativeRoute integralRoute pointwiseMetricRoute metricBoundRoute metricBoundPkg
  obtain ⟨realUnary, _limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, _provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have pointwiseMetricUnary : UnaryHistory pointwiseMetricRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary pointwiseMetricRoute
  have metricBoundUnary : UnaryHistory metricBoundRead :=
    unary_cont_closed pointwiseMetricUnary realUnary metricBoundRoute
  have sourceMetric :
      (fun row : BHist => hsame row metricBoundRead ∧ UnaryHistory row)
          metricBoundRead := by
    exact ⟨hsame_refl metricBoundRead, metricBoundUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricBoundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row integralRead ∨
              hsame row pointwiseMetricRead ∨ hsame row metricBoundRead ∨ hsame row real)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont derivativeRead integralRead pointwiseMetricRead ∧
              Cont pointwiseMetricRead real metricBoundRead ∧
                PkgSig bundle metricBoundRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricBoundRead sourceMetric
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pointwiseMetricRoute, metricBoundRoute, metricBoundPkg⟩
  }
  exact ⟨cert, pointwiseMetricUnary, metricBoundUnary⟩

end BEDC.Derived.CalculusUp
