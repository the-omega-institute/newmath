import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_terminal_pullback_consumer_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selectedRead terminal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows dyadic selector ->
        Cont selector readback selectedRead ->
          Cont selectedRead realSeal terminal ->
            Cont terminal cert consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory selector ∧
                  UnaryHistory readback ∧ UnaryHistory selectedRead ∧ UnaryHistory realSeal ∧
                    UnaryHistory terminal ∧ UnaryHistory cert ∧ UnaryHistory consumer ∧
                      Cont windows dyadic selector ∧ Cont selector readback selectedRead ∧
                        Cont selectedRead realSeal terminal ∧ Cont terminal cert consumer ∧
                          Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowsDyadicSelector selectorReadbackSelected selectedRealTerminal
    terminalCertConsumer consumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicSelector
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackSelected
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectedReadUnary realSealUnary selectedRealTerminal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalUnary certUnary terminalCertConsumer
  exact
    ⟨windowsUnary, dyadicUnary, selectorUnary, readbackUnary, selectedReadUnary,
      realSealUnary, terminalUnary, certUnary, consumerUnary, windowsDyadicSelector,
      selectorReadbackSelected, selectedRealTerminal, terminalCertConsumer,
      routeCertTransport, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
