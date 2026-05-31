import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_root_real_seal_handoff [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name realSealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow realSealRead →
        PkgSig bundle realSealRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory realSealRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow realSealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet realSealRoute realSealPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed readbackUnary sealUnary realSealRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, realSealUnary,
      filterWindows, toleranceReadback, realSealRoute, provenancePkg, realSealPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
