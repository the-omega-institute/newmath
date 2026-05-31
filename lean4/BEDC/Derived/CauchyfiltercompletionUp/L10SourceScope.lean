import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_l10_source_scope [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name realRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow realRead →
        Cont sealRow transport completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory realRead ∧
                UnaryHistory completionRead ∧ Cont filter windows tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont readback sealRow realRead ∧
                    Cont sealRow transport completionRead ∧ Cont transport replay provenance ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet readbackSeal sealTransport completionPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary readbackSeal
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary transportUnary sealTransport
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, realReadUnary,
      completionReadUnary, filterWindows, toleranceReadback, readbackSeal, sealTransport,
      transportReplay, provenancePkg, completionPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
