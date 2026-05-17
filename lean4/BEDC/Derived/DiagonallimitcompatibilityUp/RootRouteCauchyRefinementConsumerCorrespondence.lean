import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteCauchyRefinementConsumerCorrespondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      thresholdExit cauchyFace uniformExit uniformFace : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows dyadic thresholdExit ->
        Cont thresholdExit readback cauchyFace ->
          Cont windows dyadic uniformExit ->
            Cont uniformExit realSeal uniformFace ->
              PkgSig bundle cauchyFace pkg ->
                PkgSig bundle uniformFace pkg ->
                  UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory thresholdExit ∧
                      UnaryHistory cauchyFace ∧ UnaryHistory uniformExit ∧
                        UnaryHistory uniformFace ∧ Cont windows dyadic thresholdExit ∧
                          Cont thresholdExit readback cauchyFace ∧
                            Cont windows dyadic uniformExit ∧
                              Cont uniformExit realSeal uniformFace ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle cauchyFace pkg ∧
                                    PkgSig bundle uniformFace pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowsDyadicThreshold thresholdReadbackCauchy windowsDyadicUniform
    uniformRealSealFace cauchyPkg uniformPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdExit :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicThreshold
  have cauchyUnary : UnaryHistory cauchyFace :=
    unary_cont_closed thresholdUnary readbackUnary thresholdReadbackCauchy
  have uniformUnary : UnaryHistory uniformExit :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicUniform
  have uniformFaceUnary : UnaryHistory uniformFace :=
    unary_cont_closed uniformUnary realSealUnary uniformRealSealFace
  exact
    ⟨windowsUnary, dyadicUnary, readbackUnary, realSealUnary, thresholdUnary, cauchyUnary,
      uniformUnary, uniformFaceUnary, windowsDyadicThreshold, thresholdReadbackCauchy,
      windowsDyadicUniform, uniformRealSealFace, provenancePkg, cauchyPkg, uniformPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
