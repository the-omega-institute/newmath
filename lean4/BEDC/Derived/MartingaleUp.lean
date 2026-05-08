import BEDC.Derived.CondExpUp

namespace BEDC.Derived.MartingaleUp

open BEDC.Derived.CondExpUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MartingaleAdaptedSequencePacket
    (targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist) : Prop :=
  UnaryHistory sourceTotal ∧
    CondExpCarrierPacket targetTotal sourceTotal chosenPreimage integrable projected residual ∧
      UnaryHistory filtration ∧ Cont integrable filtration stepEndpoint ∧
        Cont stepEndpoint previous ledger

theorem MartingaleAdaptedSequencePacket_condexp_step_law
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal ∧
        VecSpaceSingletonClassifier projected BHist.Empty ∧
          Cont projected residual integrable ∧ Cont integrable filtration stepEndpoint ∧
            Cont stepEndpoint previous ledger := by
  intro packet
  have carrierRows := CondExpCarrier_packet packet.left packet.right.left
  have preimageRows :=
    BEDC.Derived.RandomVarUp.RandomVarTotalReadbackCertificate_total_event_preimage_exactness
      packet.left packet.right.left.left
  exact And.intro carrierRows.left
    (And.intro preimageRows.right
      (And.intro carrierRows.right.right.left
        (And.intro carrierRows.right.right.right
          (And.intro packet.right.right.right.left packet.right.right.right.right))))

end BEDC.Derived.MartingaleUp
