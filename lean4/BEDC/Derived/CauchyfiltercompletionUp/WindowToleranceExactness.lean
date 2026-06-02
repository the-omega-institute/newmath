import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_window_tolerance_exactness [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name windowRead
      readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont windows tolerance windowRead →
        Cont windowRead readback readbackRead →
          PkgSig bundle readbackRead pkg →
            UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
              Cont windows tolerance windowRead ∧ Cont windowRead readback readbackRead ∧
                Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle readbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsTolerance windowReadback readbackPkg
  obtain ⟨_filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsTolerance
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary readbackUnary windowReadback
  exact
    ⟨windowUnary, readbackReadUnary, windowsTolerance, windowReadback, toleranceReadback,
      provenancePkg, readbackPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
