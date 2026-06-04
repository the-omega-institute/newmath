import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCompletionStabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCompletionStabilityCarrier [AskSetup] [PackageSetup]
    (Q W D R E H C P N sealRead witnessRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory sealRead ∧ UnaryHistory witnessRead ∧
        Cont Q W D ∧ Cont D R sealRead ∧ Cont sealRead E witnessRead ∧
          PkgSig bundle P pkg

theorem RegularCauchyCompletionStabilityCarrier_idempotence_boundary [AskSetup]
    [PackageSetup]
    {Q W D R E H C P N sealRead witnessRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionStabilityCarrier Q W D R E H C P N sealRead witnessRead
        bundle pkg →
      Cont witnessRead C replayRead →
        PkgSig bundle replayRead pkg →
          UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
            UnaryHistory E ∧ UnaryHistory sealRead ∧ UnaryHistory witnessRead ∧
              UnaryHistory replayRead ∧ Cont Q W D ∧ Cont D R sealRead ∧
                Cont sealRead E witnessRead ∧ Cont witnessRead C replayRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier witnessReplay replayPkg
  obtain ⟨qUnary, wUnary, dUnary, rUnary, eUnary, _hUnary, cUnary, _pUnary, _nUnary,
    sealUnary, witnessUnary, qWindowDyadic, dyadicRealSeal, sealWitness,
    provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed witnessUnary cUnary witnessReplay
  exact
    ⟨qUnary, wUnary, dUnary, rUnary, eUnary, sealUnary, witnessUnary, replayUnary,
      qWindowDyadic, dyadicRealSeal, sealWitness, witnessReplay, provenancePkg, replayPkg⟩

end BEDC.Derived.RegularCauchyCompletionStabilityUp
