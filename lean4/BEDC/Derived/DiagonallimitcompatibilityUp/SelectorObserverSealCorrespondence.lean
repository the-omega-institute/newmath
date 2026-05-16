import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorObserverSealCorrespondence
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorRead observerRead selectorTerminal observerTerminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback selectorRead ->
        Cont selectorRead realSeal selectorTerminal ->
          Cont dyadic windows observerRead ->
            Cont observerRead realSeal observerTerminal ->
              hsame selectorTerminal observerTerminal ->
                PkgSig bundle selectorTerminal pkg ->
                  PkgSig bundle observerTerminal pkg ->
                    UnaryHistory selectorRead ∧ UnaryHistory observerRead ∧
                      UnaryHistory selectorTerminal ∧ UnaryHistory observerTerminal ∧
                        Cont windows readback selectorRead ∧
                          Cont selectorRead realSeal selectorTerminal ∧
                            Cont dyadic windows observerRead ∧
                              Cont observerRead realSeal observerTerminal ∧
                                hsame selectorTerminal observerTerminal ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle selectorTerminal pkg ∧
                                      PkgSig bundle observerTerminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier windowsReadbackSelector selectorRealSealTerminal dyadicWindowsObserver
    observerRealSealTerminal terminalSame selectorPkg observerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackSelector
  have observerUnary : UnaryHistory observerRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsObserver
  have selectorTerminalUnary : UnaryHistory selectorTerminal :=
    unary_cont_closed selectorUnary realSealUnary selectorRealSealTerminal
  have observerTerminalUnary : UnaryHistory observerTerminal :=
    unary_cont_closed observerUnary realSealUnary observerRealSealTerminal
  exact
    ⟨selectorUnary, observerUnary, selectorTerminalUnary, observerTerminalUnary,
      windowsReadbackSelector, selectorRealSealTerminal, dyadicWindowsObserver,
      observerRealSealTerminal, terminalSame, provenancePkg, selectorPkg, observerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
