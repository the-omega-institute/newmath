import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorSourceCoverage [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName sourceRead radiusRead precisionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes sourceRead ->
        Cont radii moduli radiusRead ->
          Cont fold precision precisionRead ->
            PkgSig bundle precisionRead pkg ->
              UnaryHistory source ∧ UnaryHistory probes ∧ UnaryHistory sourceRead ∧
                UnaryHistory radiusRead ∧ UnaryHistory precisionRead ∧
                  Cont source probes sourceRead ∧ Cont radii moduli radiusRead ∧
                    Cont fold precision precisionRead ∧ PkgSig bundle precisionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceProbesRead radiiModuliRead foldPrecisionRead precisionPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesRead
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiiUnary moduliUnary radiiModuliRead
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed foldUnary precisionUnary foldPrecisionRead
  exact
    ⟨sourceUnary, probesUnary, sourceReadUnary, radiusReadUnary, precisionReadUnary,
      sourceProbesRead, radiiModuliRead, foldPrecisionRead, precisionPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
