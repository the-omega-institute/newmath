import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LambdaCalcBHistTermPacketCarrier_public_boundary
    {graph edge connected acyclic sharedTag sharedPayload sharedEndpoint alphaTag alphaPayload
      alphaEndpoint betaTag betaPayload betaEndpoint alphaLedger betaLedger publicLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic sharedTag sharedPayload
        sharedEndpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic alphaTag alphaPayload
          alphaEndpoint ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic betaTag betaPayload
            betaEndpoint ->
          Cont sharedEndpoint alphaEndpoint alphaLedger ->
            Cont sharedEndpoint betaEndpoint betaLedger ->
              Cont alphaLedger betaLedger publicLedger ->
                UnaryHistory publicLedger ∧ hsame alphaLedger (append sharedEndpoint alphaEndpoint) ∧
                  hsame betaLedger (append sharedEndpoint betaEndpoint) ∧
                    hsame publicLedger
                      (append (append sharedEndpoint alphaEndpoint)
                        (append sharedEndpoint betaEndpoint)) := by
  intro sharedPacket alphaPacket betaPacket alphaLedgerRow betaLedgerRow publicLedgerRow
  have separated :=
    LambdaCalcBHistTermPacketCarrier_alpha_beta_ledger_separation sharedPacket alphaPacket
      betaPacket alphaLedgerRow betaLedgerRow
  have publicLedgerUnary : UnaryHistory publicLedger :=
    unary_cont_closed separated.right.left separated.right.right.left publicLedgerRow
  have publicReadback :
      hsame publicLedger
        (append (append sharedEndpoint alphaEndpoint) (append sharedEndpoint betaEndpoint)) := by
    cases separated.right.right.right.left
    cases separated.right.right.right.right
    exact publicLedgerRow
  exact And.intro publicLedgerUnary
    (And.intro separated.right.right.right.left
      (And.intro separated.right.right.right.right publicReadback))

theorem LambdaCalcBHistTermPacketCarrier_namecert_ledger_exactness
    {graph edge connected acyclic sharedTag sharedPayload sharedEndpoint alphaTag alphaPayload
      alphaEndpoint betaTag betaPayload betaEndpoint alphaLedger betaLedger publicLedger
      pkgLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic sharedTag sharedPayload
        sharedEndpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic alphaTag alphaPayload
          alphaEndpoint ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic betaTag betaPayload
            betaEndpoint ->
          Cont sharedEndpoint alphaEndpoint alphaLedger ->
            Cont sharedEndpoint betaEndpoint betaLedger ->
              Cont alphaLedger betaLedger publicLedger ->
                Cont publicLedger sharedTag pkgLedger ->
                  hsame sharedTag betaTag ->
                    hsame pkgLedger (append publicLedger betaTag) ∧
                      hsame publicLedger (append alphaLedger betaLedger) := by
  intro sharedPacket alphaPacket betaPacket alphaLedgerRow betaLedgerRow publicLedgerRow
    pkgLedgerRow sharedBeta
  have publicBoundary :=
    LambdaCalcBHistTermPacketCarrier_public_boundary sharedPacket alphaPacket betaPacket
      alphaLedgerRow betaLedgerRow publicLedgerRow
  have pkgLedgerReadback : hsame pkgLedger (append publicLedger sharedTag) :=
    pkgLedgerRow
  have packageTransport :
      hsame (append publicLedger sharedTag) (append publicLedger betaTag) := by
    cases sharedBeta
    exact hsame_refl (append publicLedger sharedTag)
  exact And.intro (hsame_trans pkgLedgerReadback packageTransport)
    (hsame_trans publicLedgerRow (hsame_refl (append alphaLedger betaLedger)))

end BEDC.Derived.LambdaCalcUp
