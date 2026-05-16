import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootSelectorTerminality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert rootWindow rootReadback rootSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows rootWindow ->
        Cont rootWindow readback rootReadback ->
          Cont rootReadback realSeal rootSeal ->
            Cont rootSeal cert terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory rootWindow ∧ UnaryHistory rootReadback ∧
                  UnaryHistory rootSeal ∧ UnaryHistory terminal ∧
                    Cont diagonal windows rootWindow ∧
                      Cont rootWindow readback rootReadback ∧
                        Cont rootReadback realSeal rootSeal ∧ Cont rootSeal cert terminal ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalWindowsRootWindow rootWindowReadbackRootReadback
    rootReadbackRealSealRootSeal rootSealCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootWindowUnary : UnaryHistory rootWindow :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsRootWindow
  have rootReadbackUnary : UnaryHistory rootReadback :=
    unary_cont_closed rootWindowUnary readbackUnary rootWindowReadbackRootReadback
  have rootSealUnary : UnaryHistory rootSeal :=
    unary_cont_closed rootReadbackUnary realSealUnary rootReadbackRealSealRootSeal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed rootSealUnary certUnary rootSealCertTerminal
  exact
    ⟨rootWindowUnary, rootReadbackUnary, rootSealUnary, terminalUnary,
      diagonalWindowsRootWindow, rootWindowReadbackRootReadback, rootReadbackRealSealRootSeal,
      rootSealCertTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
