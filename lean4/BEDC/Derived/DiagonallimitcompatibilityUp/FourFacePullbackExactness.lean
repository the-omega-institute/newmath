import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_four_face_pullback_exactness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamFace dyadicFace readbackFace sealFace terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows streamFace →
        Cont streamFace dyadic dyadicFace →
          Cont dyadicFace readback readbackFace →
            Cont readbackFace realSeal sealFace →
              Cont sealFace cert terminal →
                PkgSig bundle terminal pkg →
                  UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
                    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory cert ∧
                      UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                        UnaryHistory readbackFace ∧ UnaryHistory sealFace ∧
                          UnaryHistory terminal ∧ Cont diagonal triangle sealRow ∧
                            Cont dyadic windows readback ∧ Cont readback realSeal route ∧
                              Cont route cert transport ∧ Cont diagonal windows streamFace ∧
                                Cont streamFace dyadic dyadicFace ∧
                                  Cont dyadicFace readback readbackFace ∧
                                    Cont readbackFace realSeal sealFace ∧
                                      Cont sealFace cert terminal ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsStream streamDyadicFace dyadicReadbackFace
    readbackRealSealFace sealCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, routeCertTransport,
    provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStream
  have dyadicFaceUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicFace
  have readbackFaceUnary : UnaryHistory readbackFace :=
    unary_cont_closed dyadicFaceUnary readbackUnary dyadicReadbackFace
  have sealFaceUnary : UnaryHistory sealFace :=
    unary_cont_closed readbackFaceUnary realSealUnary readbackRealSealFace
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealFaceUnary certUnary sealCertTerminal
  exact
    ⟨diagonalUnary, windowsUnary, dyadicUnary, readbackUnary, realSealUnary, certUnary,
      streamUnary, dyadicFaceUnary, readbackFaceUnary, sealFaceUnary, terminalUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, routeCertTransport,
      diagonalWindowsStream, streamDyadicFace, dyadicReadbackFace, readbackRealSealFace,
      sealCertTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
