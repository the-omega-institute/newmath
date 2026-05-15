import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_uniform_cauchy_terminal_handoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal uIndex uWindows uModulus uTolerance uTail uSeal uTransports uRoutes uProvenance
      uName uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket uIndex uWindows
          uModulus uTolerance uTail uSeal uTransports uRoutes uProvenance uName bundle pkg ->
        Cont readback realSeal terminal ->
          Cont terminal uTail uniformRead ->
            PkgSig bundle terminal pkg ->
              PkgSig bundle uniformRead pkg ->
                UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                  UnaryHistory uIndex ∧ UnaryHistory uTail ∧ UnaryHistory uniformRead ∧
                    Cont readback realSeal terminal ∧ Cont terminal uTail uniformRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uName pkg ∧
                        PkgSig bundle terminal pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier uniformPacket readbackRealSealTerminal terminalTailUniform terminalPkg
    uniformReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  obtain ⟨uIndexUnary, _uWindowsUnary, _uModulusUnary, _uToleranceUnary, uTailUnary,
    _uSealUnary, _uTransportsUnary, _uRoutesUnary, _uProvenanceUnary, _uNameUnary,
    _uIndexWindowsModulus, _uModulusToleranceTail, _uTailSealTransports,
    _uTransportsRoutesProvenance, uNamePkg⟩ := uniformPacket
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed terminalUnary uTailUnary terminalTailUniform
  exact
    ⟨readbackUnary, realSealUnary, terminalUnary, uIndexUnary, uTailUnary,
      uniformReadUnary, readbackRealSealTerminal, terminalTailUniform, provenancePkg,
      uNamePkg, terminalPkg, uniformReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
