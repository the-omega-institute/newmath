import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalRowConstructorExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name replayRead
      replayExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont continuation transports replayRead →
        Cont replayRead routes replayExport →
          PkgSig bundle replayExport pkg →
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
                UnaryHistory routes ∧ UnaryHistory replayRead ∧ UnaryHistory replayExport ∧
                  Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
                    Cont continuation transports replayRead ∧
                      Cont replayRead routes replayExport ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle replayExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet continuationTransportsReplay replayRoutesExport replayExportPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed continuationUnary transportsUnary continuationTransportsReplay
  have replayExportUnary : UnaryHistory replayExport :=
    unary_cont_closed replayReadUnary routesUnary replayRoutesExport
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary, transportsUnary,
      routesUnary, replayReadUnary, replayExportUnary, typedFuelTerminal,
      terminalNormalContinuation, continuationTransportsReplay, replayRoutesExport,
      provenancePkg, replayExportPkg⟩

end BEDC.Derived.ZnormalUp
