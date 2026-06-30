import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_fold_radius_exhaustion [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead radiusRead foldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead ->
        Cont radii fold radiusRead ->
          Cont radiusRead precision foldRead ->
            PkgSig bundle foldRead pkg ->
              UnaryHistory compactRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory foldRead ∧ Cont source probes compactRead ∧
                  Cont radii fold radiusRead ∧ Cont radiusRead precision foldRead ∧
                    PkgSig bundle foldRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier sourceProbesCompact radiiFoldRadius radiusPrecisionFold foldReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    radiiUnary, _moduliUnary, foldUnary, precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary foldUnary radiiFoldRadius
  have foldReadUnary : UnaryHistory foldRead :=
    unary_cont_closed radiusReadUnary precisionUnary radiusPrecisionFold
  exact
    ⟨compactReadUnary, radiusReadUnary, foldReadUnary, sourceProbesCompact,
      radiiFoldRadius, radiusPrecisionFold, foldReadPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
