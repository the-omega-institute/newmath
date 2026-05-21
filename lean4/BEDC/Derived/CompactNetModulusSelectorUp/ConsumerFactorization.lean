import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorCarrier_consumer_factorization [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead modulusRead precisionRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg ->
      Cont source probes compactRead ->
        Cont moduli fold modulusRead ->
          Cont precision route precisionRead ->
            Cont precisionRead provenance uniformRead ->
              PkgSig bundle precisionRead pkg ->
                PkgSig bundle uniformRead pkg ->
                  UnaryHistory compactRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory precisionRead ∧ UnaryHistory uniformRead ∧
                      Cont source probes compactRead ∧ Cont moduli fold modulusRead ∧
                        Cont precision route precisionRead ∧
                          Cont precisionRead provenance uniformRead ∧
                            PkgSig bundle precisionRead pkg ∧
                              PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier sourceProbesCompact moduliFoldModulus precisionRouteRead
    precisionReadProvenanceUniform precisionReadPkg uniformReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, _centersUnary,
    _radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    provenanceUnary, _localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, _provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed precisionReadUnary provenanceUnary precisionReadProvenanceUniform
  exact
    ⟨compactReadUnary, modulusReadUnary, precisionReadUnary, uniformReadUnary,
      sourceProbesCompact, moduliFoldModulus, precisionRouteRead,
      precisionReadProvenanceUniform, precisionReadPkg, uniformReadPkg⟩

end BEDC.Derived.CompactNetModulusSelectorUp
