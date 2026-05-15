import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootL10SpineExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamReg dyadicSeal sealBoundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback streamReg ->
        Cont dyadic streamReg dyadicSeal ->
          Cont dyadicSeal realSeal sealBoundary ->
            Cont sealBoundary cert terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
                  UnaryHistory realSeal ∧ UnaryHistory cert ∧ UnaryHistory streamReg ∧
                    UnaryHistory dyadicSeal ∧ UnaryHistory sealBoundary ∧
                      UnaryHistory terminal ∧ Cont windows readback streamReg ∧
                        Cont dyadic streamReg dyadicSeal ∧
                          Cont dyadicSeal realSeal sealBoundary ∧
                            Cont sealBoundary cert terminal ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier windowsReadbackStream dyadicStreamSeal dyadicSealRealBoundary
    boundaryCertTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackStream
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed dyadicUnary streamRegUnary dyadicStreamSeal
  have sealBoundaryUnary : UnaryHistory sealBoundary :=
    unary_cont_closed dyadicSealUnary realSealUnary dyadicSealRealBoundary
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealBoundaryUnary certUnary boundaryCertTerminal
  exact
    ⟨windowsUnary, readbackUnary, dyadicUnary, realSealUnary, certUnary, streamRegUnary,
      dyadicSealUnary, sealBoundaryUnary, terminalUnary, windowsReadbackStream,
      dyadicStreamSeal, dyadicSealRealBoundary, boundaryCertTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
