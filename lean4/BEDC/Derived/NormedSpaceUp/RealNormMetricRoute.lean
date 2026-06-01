import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedspaceRealNormMetricRoute [AskSetup] [PackageSetup]
    {V R N M Q H T P C normRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      Cont R N normRead →
        Cont normRead M metricRead →
          PkgSig bundle P pkg →
            SemanticNameCert
                (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                    hsame row metricRead)
                (fun row : BHist => hsame row metricRead ∧ PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier normRoute metricRoute provenancePkg
  obtain ⟨_vUnary, rUnary, nUnary, mUnary, _qUnary, _hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, _carrierProvenancePkg,
    _localPkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed rUnary nUnary normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary mUnary metricRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row metricRead)
          (fun row : BHist => hsame row metricRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro metricRead ⟨hsame_refl metricRead, metricUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, metricUnary⟩

end BEDC.Derived.NormedSpaceUp
