import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_completion_reflector_consumer [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name reflectorRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow transport reflectorRead →
        PkgSig bundle reflectorRead pkg →
          UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
              UnaryHistory reflectorRead ∧ Cont filter windows tolerance ∧
                Cont tolerance readback sealRow ∧ Cont sealRow transport reflectorRead ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle reflectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet sealTransportReflector reflectorPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, transportReplay, provenancePkg, _namePkg⟩ := packet
  have reflectorUnary : UnaryHistory reflectorRead :=
    unary_cont_closed sealUnary transportUnary sealTransportReflector
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, transportUnary,
      reflectorUnary, filterWindows, toleranceReadback, sealTransportReflector,
      transportReplay, provenancePkg, reflectorPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
