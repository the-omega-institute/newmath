import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorUniqueness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamReg0 streamReg1 dyadicSeal0 dyadicSeal1 sealBoundary0 sealBoundary1 final0
      final1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback streamReg0 ->
        Cont windows readback streamReg1 ->
          Cont dyadic streamReg0 dyadicSeal0 ->
            Cont dyadic streamReg1 dyadicSeal1 ->
              Cont dyadicSeal0 realSeal sealBoundary0 ->
                Cont dyadicSeal1 realSeal sealBoundary1 ->
                  Cont sealBoundary0 cert final0 ->
                    Cont sealBoundary1 cert final1 ->
                      PkgSig bundle final0 pkg ->
                        PkgSig bundle final1 pkg ->
                          hsame streamReg0 streamReg1 ∧ hsame dyadicSeal0 dyadicSeal1 ∧
                            hsame sealBoundary0 sealBoundary1 ∧ hsame final0 final1 ∧
                              UnaryHistory final0 ∧ UnaryHistory final1 ∧
                                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier windowsReadback0 windowsReadback1 dyadicStream0 dyadicStream1
    dyadicSealReal0 dyadicSealReal1 sealBoundaryCert0 sealBoundaryCert1 _finalPkg0
    _finalPkg1
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamRegSame : hsame streamReg0 streamReg1 :=
    cont_deterministic windowsReadback0 windowsReadback1
  have streamRegUnary0 : UnaryHistory streamReg0 :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback0
  have streamRegUnary1 : UnaryHistory streamReg1 :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback1
  have dyadicSealSame : hsame dyadicSeal0 dyadicSeal1 :=
    cont_respects_hsame (hsame_refl dyadic) streamRegSame dyadicStream0 dyadicStream1
  have dyadicSealUnary0 : UnaryHistory dyadicSeal0 :=
    unary_cont_closed dyadicUnary streamRegUnary0 dyadicStream0
  have dyadicSealUnary1 : UnaryHistory dyadicSeal1 :=
    unary_cont_closed dyadicUnary streamRegUnary1 dyadicStream1
  have sealBoundarySame : hsame sealBoundary0 sealBoundary1 :=
    cont_respects_hsame dyadicSealSame (hsame_refl realSeal) dyadicSealReal0
      dyadicSealReal1
  have sealBoundaryUnary0 : UnaryHistory sealBoundary0 :=
    unary_cont_closed dyadicSealUnary0 realSealUnary dyadicSealReal0
  have sealBoundaryUnary1 : UnaryHistory sealBoundary1 :=
    unary_cont_closed dyadicSealUnary1 realSealUnary dyadicSealReal1
  have finalSame : hsame final0 final1 :=
    cont_respects_hsame sealBoundarySame (hsame_refl cert) sealBoundaryCert0
      sealBoundaryCert1
  have finalUnary0 : UnaryHistory final0 :=
    unary_cont_closed sealBoundaryUnary0 certUnary sealBoundaryCert0
  have finalUnary1 : UnaryHistory final1 :=
    unary_cont_closed sealBoundaryUnary1 certUnary sealBoundaryCert1
  exact
    ⟨streamRegSame, dyadicSealSame, sealBoundarySame, finalSame, finalUnary0, finalUnary1,
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
