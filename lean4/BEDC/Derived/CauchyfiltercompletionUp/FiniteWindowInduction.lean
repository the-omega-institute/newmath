import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_finite_window_induction [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name inductionStep : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance inductionStep →
        Cont inductionStep readback sealRow →
          PkgSig bundle inductionStep pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory inductionStep ∧
                Cont filter windows tolerance ∧ Cont windows tolerance inductionStep ∧
                  Cont inductionStep readback sealRow ∧ Cont transport replay provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle inductionStep pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowStep stepSeal stepPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have stepUnary : UnaryHistory inductionStep :=
    unary_cont_closed windowsUnary toleranceUnary windowStep
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, stepUnary,
      filterWindows, windowStep, stepSeal, transportReplay, provenancePkg, stepPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
