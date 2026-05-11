import BEDC.Derived.LambdaCalcUp

namespace BEDC.Derived.LambdaCalcUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LambdaCalcBHistTermPacketCarrier_alpha_classifier_transitive
    {graph edge connected acyclic leftTag leftPayload leftEndpoint middleTag middlePayload
      middleEndpoint rightTag rightPayload rightEndpoint leftLedger rightLedger
      composedLedger : BHist} :
    LambdaCalcBHistTermPacketCarrier graph edge connected acyclic leftTag leftPayload
        leftEndpoint ->
      LambdaCalcBHistTermPacketCarrier graph edge connected acyclic middleTag middlePayload
          middleEndpoint ->
        LambdaCalcBHistTermPacketCarrier graph edge connected acyclic rightTag rightPayload
            rightEndpoint ->
          Cont leftEndpoint middleEndpoint leftLedger ->
            Cont middleEndpoint rightEndpoint rightLedger ->
              Cont leftLedger rightLedger composedLedger ->
                UnaryHistory composedLedger ∧
                  hsame composedLedger
                    (append (append leftEndpoint middleEndpoint)
                      (append middleEndpoint rightEndpoint)) := by
  intro leftPacket middlePacket _rightPacket leftLedgerRow rightLedgerRow composedLedgerRow
  have leftLedgerUnary : UnaryHistory leftLedger :=
    unary_cont_closed leftPacket.right.right.left middlePacket.right.right.left leftLedgerRow
  have rightLedgerUnary : UnaryHistory rightLedger :=
    unary_cont_closed middlePacket.right.right.left _rightPacket.right.right.left rightLedgerRow
  have composedLedgerUnary : UnaryHistory composedLedger :=
    unary_cont_closed leftLedgerUnary rightLedgerUnary composedLedgerRow
  have composedReadback :
      hsame composedLedger
        (append (append leftEndpoint middleEndpoint) (append middleEndpoint rightEndpoint)) := by
    cases leftLedgerRow
    cases rightLedgerRow
    exact composedLedgerRow
  exact And.intro composedLedgerUnary composedReadback

end BEDC.Derived.LambdaCalcUp
