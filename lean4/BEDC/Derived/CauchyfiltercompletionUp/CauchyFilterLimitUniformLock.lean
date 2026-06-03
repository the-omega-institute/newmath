import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_cauchyfilter_limit_uniform_lock
    [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead
      limitRead uniformRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows sourceRead →
        Cont sourceRead readback limitRead →
          Cont limitRead provenance uniformRead →
            Cont uniformRead sealRow terminalRead →
              PkgSig bundle terminalRead pkg →
                UnaryHistory sourceRead ∧ UnaryHistory limitRead ∧
                  UnaryHistory uniformRead ∧ UnaryHistory terminalRead ∧
                    Cont filter windows sourceRead ∧ Cont sourceRead readback limitRead ∧
                      Cont limitRead provenance uniformRead ∧
                        Cont uniformRead sealRow terminalRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet filterWindowsSource sourceReadbackLimit limitProvenanceUniform
    uniformSealTerminal terminalPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary windowsUnary filterWindowsSource
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sourceUnary readbackUnary sourceReadbackLimit
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed limitUnary provenanceUnary limitProvenanceUniform
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed uniformUnary sealUnary uniformSealTerminal
  exact
    ⟨sourceUnary, limitUnary, uniformUnary, terminalUnary, filterWindowsSource,
      sourceReadbackLimit, limitProvenanceUniform, uniformSealTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
