import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_real_seal_source_exhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow realRead →
        PkgSig bundle realRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory realRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow realRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet readbackSeal realReadPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, realReadUnary,
      filterWindows, toleranceReadback, readbackSeal, provenancePkg, realReadPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
