import BEDC.Derived.CauchyLimitFunctorUp
import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.Derived.CauchyLimitFunctorUp
open BEDC.Derived.UniformCauchyCriterionUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityFunctorUniformTerminalFactorization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sourceSeal targetSeal transportMap sourceWindow targetWindow functorReadback tolerance
      classifier endpoint hsameRows functorRoutes functorProvenance functorNameCert
      carrierEndpoint uIndex uWindows uModulus uTolerance uTail uSeal uTransports uRoutes
      uProvenance uName terminal uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
          functorReadback tolerance classifier endpoint hsameRows functorRoutes
          functorProvenance functorNameCert carrierEndpoint bundle pkg →
        UniformCauchyCriterionPacket uIndex uWindows uModulus uTolerance uTail uSeal
            uTransports uRoutes uProvenance uName bundle pkg →
          Cont readback realSeal terminal →
            Cont carrierEndpoint realSeal terminal →
              Cont terminal uTail uniformRead →
                PkgSig bundle terminal pkg →
                  PkgSig bundle uniformRead pkg →
                    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                      UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧
                        UnaryHistory carrierEndpoint ∧ UnaryHistory uWindows ∧
                          UnaryHistory uTail ∧ UnaryHistory terminal ∧
                            UnaryHistory uniformRead ∧ Cont readback realSeal terminal ∧
                              Cont carrierEndpoint realSeal terminal ∧
                                Cont terminal uTail uniformRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle carrierEndpoint pkg ∧
                                      PkgSig bundle uName pkg ∧
                                        PkgSig bundle terminal pkg ∧
                                          PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro diagonalCarrier functorCarrier uniformPacket readbackRealSealTerminal
    carrierEndpointRealSealTerminal terminalUTailUniformRead terminalPkg uniformReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, sourceWindowUnary,
    targetWindowUnary, _functorReadbackUnary, _toleranceUnary, _classifierUnary,
    _endpointUnary, _hsameRowsUnary, _functorRoutesUnary, _functorProvenanceUnary,
    _functorNameCertUnary, carrierEndpointUnary, _sourceSealTransportTarget,
    _sourceWindowTargetWindowReadback, _functorReadbackToleranceClassifier,
    _classifierEndpointCarrierEndpoint, _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ :=
    functorCarrier
  obtain ⟨_uIndexUnary, uWindowsUnary, _uModulusUnary, _uToleranceUnary, uTailUnary,
    _uSealUnary, _uTransportsUnary, _uRoutesUnary, _uProvenanceUnary, _uNameUnary,
    _uIndexWindowsModulus, _uModulusToleranceTail, _uTailSealTransports,
    _uTransportsRoutesProvenance, uNamePkg⟩ := uniformPacket
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed terminalUnary uTailUnary terminalUTailUniformRead
  exact
    ⟨windowsUnary, readbackUnary, realSealUnary, sourceWindowUnary, targetWindowUnary,
      carrierEndpointUnary, uWindowsUnary, uTailUnary, terminalUnary, uniformReadUnary,
      readbackRealSealTerminal, carrierEndpointRealSealTerminal, terminalUTailUniformRead,
      provenancePkg, carrierEndpointPkg, uNamePkg, terminalPkg, uniformReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
