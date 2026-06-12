import BEDC.Derived.CauchyDoubleSequenceUp

namespace BEDC.Derived.CauchyDoubleSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDoubleSequenceCarrier_scoped_nonescape [AskSetup] [PackageSetup]
    {array schedule tolerance diagonal completion sealRow transport route provenance localCert
      consumer zArray zSeal zConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyDoubleSequenceCarrier array schedule tolerance diagonal completion sealRow transport route
        provenance localCert bundle pkg →
      Cont sealRow localCert consumer →
        UnaryHistory array ∧ UnaryHistory schedule ∧ UnaryHistory tolerance ∧
          UnaryHistory diagonal ∧ UnaryHistory completion ∧ UnaryHistory sealRow ∧
            UnaryHistory consumer ∧ Cont array schedule diagonal ∧
              Cont schedule tolerance diagonal ∧ Cont diagonal completion sealRow ∧
                PkgSig bundle provenance pkg ∧ (hsame array (BHist.e0 zArray) → False) ∧
                  (hsame sealRow (BHist.e0 zSeal) → False) ∧
                    (hsame consumer (BHist.e0 zConsumer) → False) := by
  -- BEDC touchpoint anchor: CauchyDoubleSequenceCarrier BHist Cont PkgSig hsame UnaryHistory
  intro carrier sealConsumer
  have arrayUnary : UnaryHistory array := carrier.left
  have scheduleUnary : UnaryHistory schedule := carrier.right.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.right.left
  have diagonalUnary : UnaryHistory diagonal := carrier.right.right.right.left
  have completionUnary : UnaryHistory completion := carrier.right.right.right.right.left
  have sealUnary : UnaryHistory sealRow := carrier.right.right.right.right.right.left
  have arrayScheduleRoute : Cont array schedule diagonal :=
    carrier.right.right.right.right.right.right.right.left
  have scheduleToleranceRoute : Cont schedule tolerance diagonal :=
    carrier.right.right.right.right.right.right.right.right.left
  have diagonalCompletionRoute : Cont diagonal completion sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have transportLocalCertRoute : Cont transport localCert route :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have routeProvenanceSeal : Cont route provenance sealRow :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have routeUnary : UnaryHistory route :=
    unary_append_left_factor (routeProvenanceSeal ▸ sealUnary)
  have localCertUnary : UnaryHistory localCert :=
    unary_append_right_factor (transportLocalCertRoute ▸ routeUnary)
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary localCertUnary sealConsumer
  have arrayNoZero : hsame array (BHist.e0 zArray) → False := by
    intro sameArray
    exact unary_no_zero_extension (unary_transport arrayUnary sameArray)
  have sealNoZero : hsame sealRow (BHist.e0 zSeal) → False := by
    intro sameSeal
    exact unary_no_zero_extension (unary_transport sealUnary sameSeal)
  have consumerNoZero : hsame consumer (BHist.e0 zConsumer) → False := by
    intro sameConsumer
    exact unary_no_zero_extension (unary_transport consumerUnary sameConsumer)
  exact
    ⟨arrayUnary, scheduleUnary, toleranceUnary, diagonalUnary, completionUnary, sealUnary,
      consumerUnary, arrayScheduleRoute, scheduleToleranceRoute, diagonalCompletionRoute, pkgSig,
      arrayNoZero, sealNoZero, consumerNoZero⟩

end BEDC.Derived.CauchyDoubleSequenceUp
