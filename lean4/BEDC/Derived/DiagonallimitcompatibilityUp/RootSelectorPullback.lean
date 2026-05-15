import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorPullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector rootWindow rootReadback rootSeal endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selector ->
        Cont selector windows rootWindow ->
          Cont rootWindow readback rootReadback ->
            Cont rootReadback realSeal rootSeal ->
              Cont rootSeal sealRow endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory selector ∧ UnaryHistory rootWindow ∧
                    UnaryHistory rootReadback ∧ UnaryHistory rootSeal ∧
                      UnaryHistory endpoint ∧ Cont diagonal dyadic selector ∧
                        Cont selector windows rootWindow ∧
                          Cont rootWindow readback rootReadback ∧
                            Cont rootReadback realSeal rootSeal ∧
                              Cont rootSeal sealRow endpoint ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier diagonalDyadicSelector selectorWindowsRootWindow
    rootWindowReadbackRootReadback rootReadbackRealSealRootSeal rootSealSealRowEndpoint
    endpointPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed selectorUnary windowsUnary selectorWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rootSealUnary sealRowUnary rootSealSealRowEndpoint
  exact
    ⟨selectorUnary, rootWindowUnary, rootReadbackUnary, rootSealUnary, endpointUnary,
      diagonalDyadicSelector, selectorWindowsRootWindow, rootWindowReadbackRootReadback,
      rootReadbackRealSealRootSeal, rootSealSealRowEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
