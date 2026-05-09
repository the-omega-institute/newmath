import BEDC.FKernel.Unary

namespace BEDC.Derived.FactorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def FactorBHistSourcePacket
    (vna centre witness typeRow ledger endpoint : BHist) : Prop :=
  UnaryHistory vna ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
    Cont vna centre ledger ∧ Cont ledger witness endpoint

theorem FactorBHistSourcePacket_trivial_centre_obligation
    {vna centre witness typeRow ledger endpoint : BHist} :
    FactorBHistSourcePacket vna centre witness typeRow ledger endpoint ->
      UnaryHistory vna ∧ UnaryHistory centre ∧ UnaryHistory witness ∧ UnaryHistory typeRow ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont vna centre ledger ∧
          Cont ledger witness endpoint := by
  intro packet
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary packet.right.right.left packet.right.right.right.right.right
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro ledgerUnary
            (And.intro endpointUnary
              (And.intro packet.right.right.right.right.left
                packet.right.right.right.right.right))))))

end BEDC.Derived.FactorUp
