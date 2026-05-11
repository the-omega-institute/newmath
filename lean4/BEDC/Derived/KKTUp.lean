import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KKTComplementarityLedger [AskSetup] [PackageSetup]
    (residual multiplier slack ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory residual ∧ UnaryHistory multiplier ∧ UnaryHistory slack ∧
    UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont residual multiplier ledger ∧
      Cont ledger slack endpoint ∧ PkgSig bundle endpoint pkg

theorem KKTComplementarityLedger_exactness [AskSetup] [PackageSetup]
    {residual multiplier slack ledger endpoint residual' multiplier' slack' ledger'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTComplementarityLedger residual multiplier slack ledger endpoint bundle pkg ->
      hsame residual residual' -> hsame multiplier multiplier' -> hsame slack slack' ->
        Cont residual' multiplier' ledger' -> Cont ledger' slack' endpoint' ->
          PkgSig bundle endpoint' pkg ->
            KKTComplementarityLedger residual' multiplier' slack' ledger' endpoint' bundle pkg ∧
              hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro packet sameResidual sameMultiplier sameSlack residualLedger' endpointLedger' pkgSig'
  have residualUnary' : UnaryHistory residual' :=
    unary_transport packet.left sameResidual
  have multiplierUnary' : UnaryHistory multiplier' :=
    unary_transport packet.right.left sameMultiplier
  have slackUnary' : UnaryHistory slack' :=
    unary_transport packet.right.right.left sameSlack
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameResidual sameMultiplier packet.right.right.right.right.right.left
      residualLedger'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed residualUnary' multiplierUnary' residualLedger'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameSlack packet.right.right.right.right.right.right.left
      endpointLedger'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary' slackUnary' endpointLedger'
  exact
    And.intro
      (And.intro residualUnary'
        (And.intro multiplierUnary'
          (And.intro slackUnary'
            (And.intro ledgerUnary'
              (And.intro endpointUnary'
                (And.intro residualLedger'
                  (And.intro endpointLedger' pkgSig')))))))
      (And.intro sameLedger sameEndpoint)

end BEDC.Derived.KKTUp
