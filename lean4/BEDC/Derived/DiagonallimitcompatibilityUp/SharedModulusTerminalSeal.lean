import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySharedModulusTerminalSeal [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert modulusWindow modulusSeal sharedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback modulusWindow ->
        Cont modulusWindow realSeal modulusSeal ->
          Cont modulusSeal cert sharedSeal ->
            PkgSig bundle sharedSeal pkg ->
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory modulusWindow ∧
                UnaryHistory realSeal ∧ UnaryHistory modulusSeal ∧ UnaryHistory cert ∧
                  UnaryHistory sharedSeal ∧ Cont windows readback modulusWindow ∧
                    Cont modulusWindow realSeal modulusSeal ∧
                      Cont modulusSeal cert sharedSeal ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sharedSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowsReadbackModulusWindow modulusWindowRealSealModulusSeal
    modulusSealCertSharedSeal sharedSealPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have modulusWindowUnary : UnaryHistory modulusWindow :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackModulusWindow
  have modulusSealUnary : UnaryHistory modulusSeal :=
    unary_cont_closed modulusWindowUnary realSealUnary modulusWindowRealSealModulusSeal
  have sharedSealUnary : UnaryHistory sharedSeal :=
    unary_cont_closed modulusSealUnary certUnary modulusSealCertSharedSeal
  exact
    ⟨windowsUnary, readbackUnary, modulusWindowUnary, realSealUnary, modulusSealUnary,
      certUnary, sharedSealUnary, windowsReadbackModulusWindow,
      modulusWindowRealSealModulusSeal, modulusSealCertSharedSeal, provenancePkg,
      sharedSealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
