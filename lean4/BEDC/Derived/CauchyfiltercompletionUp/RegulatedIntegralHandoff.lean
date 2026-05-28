import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_regulated_integral_handoff [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name regulatedRead
      integralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont windows readback regulatedRead ->
        Cont regulatedRead sealRow integralRead ->
          PkgSig bundle integralRead pkg ->
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory regulatedRead ∧
                UnaryHistory integralRead ∧ Cont filter windows tolerance ∧
                  Cont windows readback regulatedRead ∧ Cont regulatedRead sealRow integralRead ∧
                    Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle integralRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet windowsReadback regulatedSeal integralPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    _toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have regulatedUnary : UnaryHistory regulatedRead :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed regulatedUnary sealUnary regulatedSeal
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, regulatedUnary,
      integralUnary, filterWindows, windowsReadback, regulatedSeal, transportReplay,
      provenancePkg, integralPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
