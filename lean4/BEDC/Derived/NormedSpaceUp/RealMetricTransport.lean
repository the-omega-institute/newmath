import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_real_metric_transport [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead transportedMetric : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      Cont R N normRead →
        Cont normRead M metricRead →
          Cont metricRead H transportedMetric →
            PkgSig bundle transportedMetric pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row transportedMetric ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row N ∨ hsame row M ∨ hsame row H ∨
                      hsame row normRead ∨ hsame row metricRead ∨
                        hsame row transportedMetric)
                  (fun row : BHist =>
                    hsame row transportedMetric ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle transportedMetric pkg)
                  hsame ∧
                UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                  UnaryHistory transportedMetric := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier normRoute metricRoute transportRoute transportPkg
  obtain ⟨_vUnary, rUnary, nUnary, mUnary, _qUnary, hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed rUnary nUnary normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary mUnary metricRoute
  have transportedUnary : UnaryHistory transportedMetric :=
    unary_cont_closed metricUnary hUnary transportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedMetric ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row M ∨ hsame row H ∨
              hsame row normRead ∨ hsame row metricRead ∨ hsame row transportedMetric)
          (fun row : BHist =>
            hsame row transportedMetric ∧ PkgSig bundle P pkg ∧
              PkgSig bundle transportedMetric pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedMetric
          ⟨hsame_refl transportedMetric, transportedUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, transportPkg⟩
  }
  exact ⟨cert, normUnary, metricUnary, transportedUnary⟩

end BEDC.Derived.NormedSpaceUp
