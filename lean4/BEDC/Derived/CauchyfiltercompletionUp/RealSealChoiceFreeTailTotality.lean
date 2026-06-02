import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_real_seal_choice_free_tail_totality
    [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont readback sealRow tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory tailRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont readback sealRow tailRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet readbackSealTail tailPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealTail
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, tailUnary,
      filterWindows, toleranceReadback, readbackSealTail, provenancePkg, tailPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
