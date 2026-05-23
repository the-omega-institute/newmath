import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_metric_consumer_boundary [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead modulusRead precisionRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli fold
        precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead ->
        Cont moduli fold modulusRead ->
          Cont precision route precisionRead ->
            Cont compactRead precisionRead metricRead ->
              PkgSig bundle metricRead pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactRead ∨ hsame row modulusRead ∨
                      hsame row precisionRead ∨ hsame row metricRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle metricRead pkg ∧
                      hsame row metricRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceProbesCompact moduliFoldModulus precisionRouteRead metricRoute
    metricReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed compactReadUnary precisionReadUnary metricRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro metricRead ⟨hsame_refl metricRead, metricReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, metricReadPkg, source.left⟩
  }

end BEDC.Derived.CompactNetModulusSelectorUp
