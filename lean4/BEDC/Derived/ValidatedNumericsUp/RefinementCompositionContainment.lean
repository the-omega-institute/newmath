import BEDC.Derived.ValidatedNumericsUp

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ValidatedNumericsPacket_refinement_composition_containment [AskSetup] [PackageSetup]
    {interval precision0 precision1 precision2 modulus observation0 observation1 observation2
      readback transport containment0 containment1 containment2 provenance name0 name1 name2
      terminalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision0 modulus observation0 readback transport containment0
        provenance name0 bundle pkg ->
      hsame precision0 precision1 ->
        hsame observation0 observation1 ->
          hsame containment0 containment1 ->
            hsame name0 name1 ->
              Cont precision1 modulus observation1 ->
                Cont observation1 interval containment1 ->
                  PkgSig bundle name1 pkg ->
                    hsame precision1 precision2 ->
                      hsame observation1 observation2 ->
                        hsame containment1 containment2 ->
                          hsame name1 name2 ->
                            Cont precision2 modulus observation2 ->
                              Cont observation2 interval containment2 ->
                                Cont observation2 readback terminalRead ->
                                  Cont interval containment2 sealRead ->
                                    PkgSig bundle name2 pkg ->
                                      PkgSig bundle sealRead pkg ->
                                        ValidatedNumericsPacket interval precision2 modulus
                                            observation2 readback transport containment2
                                            provenance name2 bundle pkg ∧
                                          UnaryHistory terminalRead ∧ UnaryHistory sealRead ∧
                                            Cont observation2 readback terminalRead ∧
                                              Cont interval containment2 sealRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet samePrecision01 sameObservation01 sameContainment01 sameName01
  intro routePrecision1 routeContainment1 pkgName1
  intro samePrecision12 sameObservation12 sameContainment12 sameName12
  intro routePrecision2 routeContainment2 routeTerminal routeSeal pkgName2 _pkgSeal
  have step1 :=
    ValidatedNumericsPacket_precision_refinement_containment
      (interval := interval) (precision := precision0) (modulus := modulus)
      (observation := observation0) (readback := readback) (transport := transport)
      (containment := containment0) (provenance := provenance) (name := name0)
      (refinedPrecision := precision1) (refinedObservation := observation1)
      (refinedContainment := containment1) (refinedName := name1) (bundle := bundle)
      (pkg := pkg) packet samePrecision01 sameObservation01 sameContainment01 sameName01
      routePrecision1 routeContainment1 pkgName1
  have step2 :=
    ValidatedNumericsPacket_precision_refinement_containment
      (interval := interval) (precision := precision1) (modulus := modulus)
      (observation := observation1) (readback := readback) (transport := transport)
      (containment := containment1) (provenance := provenance) (name := name1)
      (refinedPrecision := precision2) (refinedObservation := observation2)
      (refinedContainment := containment2) (refinedName := name2) (bundle := bundle)
      (pkg := pkg) step1.left samePrecision12 sameObservation12 sameContainment12 sameName12
      routePrecision2 routeContainment2 pkgName2
  obtain ⟨intervalUnary, _precisionUnary, _modulusUnary, observationUnary, readbackUnary,
    _transportUnary, containmentUnary, _provenanceUnary, _nameUnary, _routePrecision,
    _routeReadback, _routeContainment, _routeName, _namePkg⟩ := step2.left
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed observationUnary readbackUnary routeTerminal
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary containmentUnary routeSeal
  exact ⟨step2.left, terminalUnary, sealUnary, routeTerminal, routeSeal⟩

end BEDC.Derived.ValidatedNumericsUp
