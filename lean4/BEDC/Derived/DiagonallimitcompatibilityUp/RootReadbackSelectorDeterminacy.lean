import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootReadbackSelectorDeterminacy
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      root0 root1 window0 window1 selector0 selector1 endpoint0 endpoint1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic root0 ->
      Cont diagonal dyadic root1 ->
      Cont root0 windows window0 ->
      Cont root1 windows window1 ->
      Cont window0 readback selector0 ->
      Cont window1 readback selector1 ->
      Cont selector0 realSeal endpoint0 ->
      Cont selector1 realSeal endpoint1 ->
      PkgSig bundle endpoint0 pkg ->
      PkgSig bundle endpoint1 pkg ->
        hsame root0 root1 /\ hsame window0 window1 /\ hsame selector0 selector1 /\
          hsame endpoint0 endpoint1 /\ UnaryHistory endpoint0 /\ UnaryHistory endpoint1 /\
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalDyadicRoot0 diagonalDyadicRoot1 root0WindowsWindow0
    root1WindowsWindow1 window0ReadbackSelector0 window1ReadbackSelector1
    selector0RealSealEndpoint0 selector1RealSealEndpoint1 _endpointPkg0 _endpointPkg1
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootSame : hsame root0 root1 :=
    cont_deterministic diagonalDyadicRoot0 diagonalDyadicRoot1
  have rootUnary0 : UnaryHistory root0 :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot0
  have rootUnary1 : UnaryHistory root1 :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot1
  have windowSame : hsame window0 window1 :=
    cont_respects_hsame rootSame (hsame_refl windows) root0WindowsWindow0
      root1WindowsWindow1
  have windowUnary0 : UnaryHistory window0 :=
    unary_cont_closed rootUnary0 windowsUnary root0WindowsWindow0
  have windowUnary1 : UnaryHistory window1 :=
    unary_cont_closed rootUnary1 windowsUnary root1WindowsWindow1
  have selectorSame : hsame selector0 selector1 :=
    cont_respects_hsame windowSame (hsame_refl readback) window0ReadbackSelector0
      window1ReadbackSelector1
  have selectorUnary0 : UnaryHistory selector0 :=
    unary_cont_closed windowUnary0 readbackUnary window0ReadbackSelector0
  have selectorUnary1 : UnaryHistory selector1 :=
    unary_cont_closed windowUnary1 readbackUnary window1ReadbackSelector1
  have endpointSame : hsame endpoint0 endpoint1 :=
    cont_respects_hsame selectorSame (hsame_refl realSeal) selector0RealSealEndpoint0
      selector1RealSealEndpoint1
  have endpointUnary0 : UnaryHistory endpoint0 :=
    unary_cont_closed selectorUnary0 realSealUnary selector0RealSealEndpoint0
  have endpointUnary1 : UnaryHistory endpoint1 :=
    unary_cont_closed selectorUnary1 realSealUnary selector1RealSealEndpoint1
  exact
    ⟨rootSame, windowSame, selectorSame, endpointSame, endpointUnary0, endpointUnary1,
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
