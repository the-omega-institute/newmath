import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_seal_factorization_obligation [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow transport completionConsumer →
        PkgSig bundle completionConsumer pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
              UnaryHistory completionConsumer ∧ Cont filter windows tolerance ∧
                Cont tolerance readback sealRow ∧ Cont sealRow transport completionConsumer ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle completionConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet sealTransport completionPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed sealUnary transportUnary sealTransport
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, transportUnary,
      completionUnary, filterWindows, toleranceReadback, sealTransport, transportReplay,
      provenancePkg, completionPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
