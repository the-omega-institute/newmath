import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityFourFaceBudgetDeterminacy [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamFace regFace realFace auditFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows streamFace ->
        Cont dyadic readback regFace ->
          Cont streamFace regFace realFace ->
            Cont realFace cert auditFace ->
              PkgSig bundle auditFace pkg ->
                UnaryHistory streamFace ∧ UnaryHistory dyadic ∧ UnaryHistory regFace ∧
                  UnaryHistory realSeal ∧ UnaryHistory realFace ∧ UnaryHistory auditFace ∧
                    Cont diagonal windows streamFace ∧ Cont dyadic readback regFace ∧
                      Cont streamFace regFace realFace ∧ Cont realFace cert auditFace ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle auditFace pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsStreamFace dyadicReadbackRegFace streamRegRealFace
    realCertAuditFace auditFacePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStreamFace
  have regFaceUnary : UnaryHistory regFace :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackRegFace
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed streamFaceUnary regFaceUnary streamRegRealFace
  have auditFaceUnary : UnaryHistory auditFace :=
    unary_cont_closed realFaceUnary certUnary realCertAuditFace
  exact
    ⟨streamFaceUnary, dyadicUnary, regFaceUnary, realSealUnary, realFaceUnary,
      auditFaceUnary, diagonalWindowsStreamFace, dyadicReadbackRegFace, streamRegRealFace,
      realCertAuditFace, provenancePkg, auditFacePkg⟩

theorem DiagonalLimitCompatibilityCarrier_four_face_budget_determinacy
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamFace0 streamFace1 regFace0 regFace1 realFace0 realFace1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows streamFace0 ->
        Cont diagonal windows streamFace1 ->
          Cont dyadic readback regFace0 ->
            Cont dyadic readback regFace1 ->
              Cont streamFace0 regFace0 realFace0 ->
                Cont streamFace1 regFace1 realFace1 ->
                  PkgSig bundle realFace0 pkg ->
                    PkgSig bundle realFace1 pkg ->
                      hsame streamFace0 streamFace1 ∧ hsame regFace0 regFace1 ∧
                        hsame realFace0 realFace1 ∧ UnaryHistory streamFace0 ∧
                          UnaryHistory streamFace1 ∧ UnaryHistory regFace0 ∧
                            UnaryHistory regFace1 ∧ UnaryHistory realFace0 ∧
                              UnaryHistory realFace1 ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  intro carrier diagonalWindowsStream0 diagonalWindowsStream1 dyadicReadbackReg0
    dyadicReadbackReg1 streamRegReal0 streamRegReal1 _realFace0Pkg _realFace1Pkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sameStream : hsame streamFace0 streamFace1 :=
    cont_deterministic diagonalWindowsStream0 diagonalWindowsStream1
  have sameReg : hsame regFace0 regFace1 :=
    cont_deterministic dyadicReadbackReg0 dyadicReadbackReg1
  have sameReal : hsame realFace0 realFace1 :=
    cont_respects_hsame sameStream sameReg streamRegReal0 streamRegReal1
  have stream0Unary : UnaryHistory streamFace0 :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStream0
  have stream1Unary : UnaryHistory streamFace1 :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStream1
  have reg0Unary : UnaryHistory regFace0 :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackReg0
  have reg1Unary : UnaryHistory regFace1 :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackReg1
  have real0Unary : UnaryHistory realFace0 :=
    unary_cont_closed stream0Unary reg0Unary streamRegReal0
  have real1Unary : UnaryHistory realFace1 :=
    unary_cont_closed stream1Unary reg1Unary streamRegReal1
  exact
    ⟨sameStream, sameReg, sameReal, stream0Unary, stream1Unary, reg0Unary, reg1Unary,
      real0Unary, real1Unary, provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
