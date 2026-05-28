import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyFilterCompletionRealSealUniquenessRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sealRead
      sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      hsame sealRow sealRead ->
        hsame sealRow sealRead' ->
          hsame sealRead sealRead' ∧ Cont filter windows tolerance ∧
            Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont PkgSig
  intro packet sameSealRead sameSealRead'
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  exact
    ⟨hsame_trans (hsame_symm sameSealRead) sameSealRead', filterWindows, toleranceReadback,
      provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
