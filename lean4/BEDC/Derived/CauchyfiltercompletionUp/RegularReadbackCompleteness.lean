import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRegularReadbackCompleteness [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      acceptedWindow acceptedTolerance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance acceptedWindow →
        Cont acceptedWindow tolerance acceptedTolerance →
          Cont acceptedTolerance readback sealRow →
            PkgSig bundle acceptedWindow pkg →
              PkgSig bundle acceptedTolerance pkg →
                UnaryHistory readback ∧ UnaryHistory acceptedWindow ∧
                  UnaryHistory acceptedTolerance ∧ Cont acceptedTolerance readback sealRow ∧
                    Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsTolerance acceptedWindowTolerance acceptedToleranceReadback
    _acceptedWindowPkg _acceptedTolerancePkg
  obtain ⟨_filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have acceptedWindowUnary : UnaryHistory acceptedWindow :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  have acceptedToleranceUnary : UnaryHistory acceptedTolerance :=
    unary_cont_closed acceptedWindowUnary toleranceUnary acceptedWindowTolerance
  exact
    ⟨readbackUnary, acceptedWindowUnary, acceptedToleranceUnary,
      acceptedToleranceReadback, toleranceReadback, provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
