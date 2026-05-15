import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityUniformWindowRealSealPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      uniformSource uniformModulus uniformTail sharedWindow sharedReadback diagonalSeal uniformSeal
      commonConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory uniformSource ->
        UnaryHistory uniformModulus ->
          UnaryHistory uniformSeal ->
            Cont dyadic windows sharedWindow ->
              Cont sharedWindow readback sharedReadback ->
                Cont sharedReadback realSeal diagonalSeal ->
                  Cont uniformSource uniformModulus uniformTail ->
                    Cont uniformTail sharedWindow sharedReadback ->
                      Cont sharedReadback uniformSeal commonConsumer ->
                        PkgSig bundle commonConsumer pkg ->
                          UnaryHistory sharedWindow ∧ UnaryHistory sharedReadback ∧
                            UnaryHistory diagonalSeal ∧ UnaryHistory uniformTail ∧
                              UnaryHistory commonConsumer ∧ Cont dyadic windows sharedWindow ∧
                                Cont sharedWindow readback sharedReadback ∧
                                  Cont sharedReadback realSeal diagonalSeal ∧
                                    Cont uniformSource uniformModulus uniformTail ∧
                                      Cont uniformTail sharedWindow sharedReadback ∧
                                        Cont sharedReadback uniformSeal commonConsumer ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle commonConsumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier uniformSourceUnary uniformModulusUnary uniformSealUnary dyadicWindowsShared
    sharedReadbackRoute readbackRealSealDiagonal uniformSourceModulusTail
    uniformTailSharedReadback sharedUniformConsumer consumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sharedWindowUnary : UnaryHistory sharedWindow :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsShared
  have sharedReadbackUnary : UnaryHistory sharedReadback :=
    unary_cont_closed sharedWindowUnary readbackUnary sharedReadbackRoute
  have diagonalSealUnary : UnaryHistory diagonalSeal :=
    unary_cont_closed sharedReadbackUnary realSealUnary readbackRealSealDiagonal
  have uniformTailUnary : UnaryHistory uniformTail :=
    unary_cont_closed uniformSourceUnary uniformModulusUnary uniformSourceModulusTail
  have commonConsumerUnary : UnaryHistory commonConsumer :=
    unary_cont_closed sharedReadbackUnary uniformSealUnary sharedUniformConsumer
  exact
    ⟨sharedWindowUnary, sharedReadbackUnary, diagonalSealUnary, uniformTailUnary,
      commonConsumerUnary, dyadicWindowsShared, sharedReadbackRoute, readbackRealSealDiagonal,
      uniformSourceModulusTail, uniformTailSharedReadback, sharedUniformConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
