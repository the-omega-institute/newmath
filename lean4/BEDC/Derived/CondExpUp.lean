import BEDC.Derived.HilbertUp
import BEDC.Derived.RandomVarUp

namespace BEDC.Derived.CondExpUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.RandomVarUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CondExpCarrierPacket
    (targetTotal sourceTotal chosenPreimage integrable projected residual : BHist) : Prop :=
  RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ∧
    HilbertSingletonProjectionWitness integrable projected ∧
      Cont projected residual integrable

theorem CondExpCarrier_packet
    {targetTotal sourceTotal chosenPreimage integrable projected residual : BHist} :
    UnaryHistory sourceTotal ->
      CondExpCarrierPacket targetTotal sourceTotal chosenPreimage integrable projected residual ->
        UnaryHistory chosenPreimage ∧ VecSpaceSingletonCarrier projected ∧
          VecSpaceSingletonClassifier projected BHist.Empty ∧
            Cont projected residual integrable := by
  intro sourceUnary packet
  have preimageRows :=
    RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary packet.left
  exact And.intro preimageRows.left
    (And.intro packet.right.left.right.left
      (And.intro packet.right.left.right.right.left packet.right.right))

theorem CondExpClassifier_obligation
    {targetTotal sourceTotal chosenPreimage integrable projected residual targetTotal' sourceTotal'
      chosenPreimage' integrable' projected' residual' : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory sourceTotal' ->
      CondExpCarrierPacket targetTotal sourceTotal chosenPreimage integrable projected residual ->
        CondExpCarrierPacket targetTotal' sourceTotal' chosenPreimage' integrable' projected'
          residual' ->
          hsame sourceTotal sourceTotal' -> hsame projected projected' ->
            hsame residual residual' ->
              hsame chosenPreimage chosenPreimage' ∧
                VecSpaceSingletonClassifier projected projected' ∧
                  hsame integrable integrable' ∧ Cont projected residual integrable ∧
                    Cont projected' residual' integrable' := by
  intro sourceUnary sourceUnary' packet packet' sameSource sameProjected sameResidual
  have preimageRows :=
    RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary packet.left
  have preimageRows' :=
    RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary' packet'.left
  have samePreimage : hsame chosenPreimage chosenPreimage' :=
    hsame_trans preimageRows.right (hsame_trans sameSource (hsame_symm preimageRows'.right))
  have projectedClassifier : VecSpaceSingletonClassifier projected projected' :=
    And.intro packet.right.left.right.left
      (And.intro packet'.right.left.right.left sameProjected)
  have sameIntegrable : hsame integrable integrable' :=
    cont_respects_hsame sameProjected sameResidual packet.right.right packet'.right.right
  exact And.intro samePreimage
    (And.intro projectedClassifier
      (And.intro sameIntegrable (And.intro packet.right.right packet'.right.right)))

end BEDC.Derived.CondExpUp
