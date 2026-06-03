import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filterbase_totality [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name filterbaseRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows filterbaseRead →
        Cont filterbaseRead readback terminalRead →
          PkgSig bundle terminalRead pkg →
            UnaryHistory filterbaseRead ∧ UnaryHistory terminalRead ∧
              Cont filter windows filterbaseRead ∧ Cont filterbaseRead readback terminalRead ∧
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterWindowsFilterbase filterbaseReadbackTerminal terminalPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbaseRead :=
    unary_cont_closed filterUnary windowsUnary filterWindowsFilterbase
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed filterbaseUnary readbackUnary filterbaseReadbackTerminal
  exact
    ⟨filterbaseUnary, terminalUnary, filterWindowsFilterbase, filterbaseReadbackTerminal,
      filterWindows, toleranceReadback, provenancePkg, terminalPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
