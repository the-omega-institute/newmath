import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_root_uniform_filter_readback [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead
      regularRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows sourceRead →
        Cont sourceRead tolerance regularRead →
          Cont regularRead sealRow terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory sourceRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory terminalRead ∧
                    Cont filter windows sourceRead ∧
                      Cont sourceRead tolerance regularRead ∧
                        Cont regularRead sealRow terminalRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sourceRoute regularRoute terminalRoute terminalPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealRowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary windowsUnary sourceRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sourceUnary toleranceUnary regularRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed regularUnary sealRowUnary terminalRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealRowUnary, sourceUnary,
      regularUnary, terminalUnary, sourceRoute, regularRoute, terminalRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
