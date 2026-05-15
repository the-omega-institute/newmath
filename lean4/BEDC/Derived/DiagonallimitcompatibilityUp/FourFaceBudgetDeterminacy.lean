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

end BEDC.Derived.DiagonallimitcompatibilityUp
