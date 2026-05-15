import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_four_face_budget_ownership [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamFace regFace realFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows streamFace →
        Cont dyadic readback regFace →
          Cont streamFace regFace realFace →
            PkgSig bundle realFace pkg →
              UnaryHistory streamFace ∧ UnaryHistory dyadic ∧ UnaryHistory regFace ∧
                UnaryHistory realSeal ∧ UnaryHistory realFace ∧
                  Cont diagonal windows streamFace ∧ Cont dyadic readback regFace ∧
                    Cont streamFace regFace realFace ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realFace pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsStreamFace dyadicReadbackRegFace streamRegRealFace realFacePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStreamFace
  have regFaceUnary : UnaryHistory regFace :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackRegFace
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed streamFaceUnary regFaceUnary streamRegRealFace
  exact
    ⟨streamFaceUnary, dyadicUnary, regFaceUnary, realSealUnary, realFaceUnary,
      diagonalWindowsStreamFace, dyadicReadbackRegFace, streamRegRealFace, provenancePkg,
      realFacePkg⟩

theorem DiagonalLimitCompatibilityCarrier_four_face_budget_ownership
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      fourFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont sealRow windows fourFace ->
        PkgSig bundle fourFace pkg ->
          UnaryHistory sealRow ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
                UnaryHistory fourFace ∧ Cont sealRow windows fourFace ∧
                  Cont dyadic windows readback ∧ Cont readback realSeal route ∧
                    Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle fourFace pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier sealRowWindowsFourFace fourFacePkg
  obtain ⟨_diagonalUnary, _triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
    _diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have fourFaceUnary : UnaryHistory fourFace :=
    unary_cont_closed sealRowUnary windowsUnary sealRowWindowsFourFace
  exact
    ⟨sealRowUnary, windowsUnary, dyadicUnary, readbackUnary, realSealUnary,
      transportUnary, routeUnary, provenanceUnary, certUnary, fourFaceUnary,
      sealRowWindowsFourFace, dyadicWindowsReadback, readbackRealSealRoute,
      routeCertTransport, provenancePkg, fourFacePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
