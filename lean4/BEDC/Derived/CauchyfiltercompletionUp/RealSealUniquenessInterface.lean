import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRealSealUniquenessInterface [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      sealRead sealRead' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      hsame sealRow sealRead →
        hsame sealRow sealRead' →
          hsame sealRead sealRead' ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
            UnaryHistory provenance ∧ UnaryHistory name ∧ Cont filter windows tolerance ∧
              Cont tolerance readback sealRow ∧ Cont transport replay provenance ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro packet sealReadSame sealReadSame'
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, _sealUnary,
    transportUnary, replayUnary, provenanceUnary, nameUnary, filterWindows, toleranceReadback,
    transportReplay, provenancePkg, namePkg⟩ := packet
  exact
    ⟨hsame_trans (hsame_symm sealReadSame) sealReadSame', transportUnary, replayUnary,
      provenanceUnary, nameUnary, filterWindows, toleranceReadback, transportReplay,
      provenancePkg, namePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
