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

theorem MartingaleAdaptedSequencePacket_condexp_ledger_stability
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger targetTotal' sourceTotal' chosenPreimage' integrable' projected'
      residual' previous' filtration' stepEndpoint' ledger' : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      MartingaleAdaptedSequencePacket targetTotal' sourceTotal' chosenPreimage' integrable'
        projected' residual' previous' filtration' stepEndpoint' ledger' ->
        hsame projected projected' ->
          hsame residual residual' ->
            hsame filtration filtration' ->
              hsame previous previous' ->
                Cont integrable filtration stepEndpoint ∧ Cont stepEndpoint previous ledger ∧
                  Cont integrable' filtration' stepEndpoint' ∧
                    Cont stepEndpoint' previous' ledger' ∧ hsame integrable integrable' ∧
                      hsame stepEndpoint stepEndpoint' ∧ hsame ledger ledger' := by
  intro packet packet' sameProjected sameResidual sameFiltration samePrevious
  have rows := MartingaleAdaptedSequencePacket_condexp_step_law packet
  have rows' := MartingaleAdaptedSequencePacket_condexp_step_law packet'
  have sameIntegrable : hsame integrable integrable' :=
    cont_respects_hsame sameProjected sameResidual rows.right.right.right.left
      rows'.right.right.right.left
  have sameStepEndpoint : hsame stepEndpoint stepEndpoint' :=
    cont_respects_hsame sameIntegrable sameFiltration rows.right.right.right.right.left
      rows'.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameStepEndpoint samePrevious rows.right.right.right.right.right
      rows'.right.right.right.right.right
  exact And.intro rows.right.right.right.right.left
    (And.intro rows.right.right.right.right.right
      (And.intro rows'.right.right.right.right.left
        (And.intro rows'.right.right.right.right.right
          (And.intro sameIntegrable
            (And.intro sameStepEndpoint sameLedger)))))

theorem MartingaleAdaptedSequencePacket_adapted_sequence_carrier_boundary
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      UnaryHistory sourceTotal ∧ UnaryHistory chosenPreimage ∧
        hsame chosenPreimage sourceTotal ∧ VecSpaceSingletonClassifier projected BHist.Empty ∧
          Cont projected residual integrable ∧ Cont integrable filtration stepEndpoint ∧
            Cont stepEndpoint previous ledger := by
  intro packet
  have rows := MartingaleAdaptedSequencePacket_condexp_step_law packet
  exact And.intro packet.left
    (And.intro rows.left
      (And.intro rows.right.left
        (And.intro rows.right.right.left
          (And.intro rows.right.right.right.left
            (And.intro rows.right.right.right.right.left
              rows.right.right.right.right.right)))))

end BEDC.Derived.MartingaleUp
