import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filterbase_window_exactness [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name filterbaseRead
      windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows filterbaseRead →
        Cont filterbaseRead tolerance windowRead →
          PkgSig bundle windowRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory filterbaseRead ∧ UnaryHistory windowRead ∧
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  Cont filter windows filterbaseRead ∧
                    Cont filterbaseRead tolerance windowRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet filterbaseRoute windowRoute windowPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have filterbaseUnary : UnaryHistory filterbaseRead :=
    unary_cont_closed filterUnary windowsUnary filterbaseRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterbaseUnary toleranceUnary windowRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, filterbaseUnary,
      windowUnary, filterWindows, toleranceReadback, filterbaseRoute, windowRoute, provenancePkg,
      windowPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
