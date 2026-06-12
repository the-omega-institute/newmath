import BEDC.Derived.CauchyDoubleSequenceUp

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDoubleSequenceSealNonEscape [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
            UnaryHistory consumer ∧ Cont array schedule diagonal ∧
              Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                Cont sealRow localCert consumer ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist Cont PkgSig UnaryHistory
  intro carrier sealConsumer
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have handoff :
      UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
        UnaryHistory consumer ∧ Cont array schedule diagonal ∧
          Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
            PkgSig bundle provenance pkg :=
    CauchyDoubleSequenceCarrier_diagonal_handoff carrier sealConsumer
  obtain ⟨diagonalUnary, completionUnary, sealUnary, consumerUnary, arrayScheduleRoute,
    scheduleToleranceRoute, diagonalCompletionRoute, provenancePkg⟩ := handoff
  exact
    ⟨arrayUnary, scheduleUnary, toleranceUnary, diagonalUnary, completionUnary, sealUnary,
      consumerUnary, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute,
      sealConsumer, provenancePkg⟩

end BEDC.Derived.CauchyDoubleSequenceUp
