import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LambdaCalcBHistTermPacketCarrier_alpha_beta_constructor_transport
    {graph edge connected acyclic tag tag' payload endpoint endpoint' substTag substPayload
      substEndpoint substEndpoint' ledger ledger' varIndex result result' : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic substTag substPayload
          substEndpoint ->
        hsame tag tag' ->
          hsame endpoint endpoint' ->
            hsame substEndpoint substEndpoint' ->
              UnaryHistory varIndex ->
                Cont endpoint substEndpoint ledger ->
                  Cont endpoint' substEndpoint' ledger' ->
                    Cont ledger varIndex result ->
                      Cont ledger' varIndex result' ->
                        hsame ledger ledger' ∧ hsame result result' := by
  intro _packet _substPacket _sameTag sameEndpoint sameSubstEndpoint _varUnary ledgerRow
    ledgerRow' resultRow resultRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameSubstEndpoint ledgerRow ledgerRow'
  have sameResult : hsame result result' :=
    cont_respects_hsame sameLedger (hsame_refl varIndex) resultRow resultRow'
  exact And.intro sameLedger sameResult

theorem LambdaCalcBHistTermPacketCarrier_namecert_classifier_stability
    {graph edge connected acyclic tag tag' payload payload' endpoint endpoint' constructorLedger
      constructorLedger' : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag payload endpoint ->
      hsame tag tag' ->
        hsame payload payload' ->
          hsame endpoint endpoint' ->
            Cont endpoint payload constructorLedger ->
              Cont endpoint' payload' constructorLedger' ->
                LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag' payload'
                    endpoint' ∧ hsame constructorLedger constructorLedger' := by
  intro packet sameTag samePayload sameEndpoint constructorRow constructorRow'
  have treeCarrier' :=
    (BEDC.Derived.TreeUp.TreeBHistCarrier_classifier_transport packet.left (hsame_refl graph)
      (hsame_refl edge) (hsame_refl connected) (hsame_refl acyclic) sameTag sameEndpoint).left
  have payloadUnary' : UnaryHistory payload' :=
    unary_transport packet.right.left samePayload
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.left sameEndpoint
  have endpointRow' : Cont tag' payload' endpoint' :=
    cont_hsame_transport sameTag samePayload sameEndpoint packet.right.right.right
  have transportedPacket :
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic tag' payload' endpoint' :=
    And.intro treeCarrier' (And.intro payloadUnary' (And.intro endpointUnary' endpointRow'))
  have sameConstructorLedger : hsame constructorLedger constructorLedger' :=
    cont_respects_hsame sameEndpoint samePayload constructorRow constructorRow'
  exact And.intro transportedPacket sameConstructorLedger

end BEDC.Derived.LambdaCalcUp
