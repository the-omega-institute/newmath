import BEDC.Derived.HilbertUp
import BEDC.Derived.RandomVarUp
import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary

namespace BEDC.Derived.CondExpUp

open BEDC.Derived.HilbertUp
open BEDC.Derived.RandomVarUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CondExpCarrier_obligation {targetTotal sourceTotal preX x p residual : BHist} :
    RandomVarTotalReadbackCertificate targetTotal sourceTotal preX ->
      HilbertSingletonProjectionWitness x p ->
        Cont p residual x ->
          hsame preX sourceTotal ∧ VecSpaceSingletonCarrier x ∧ VecSpaceSingletonCarrier p ∧
            VecSpaceSingletonCarrier residual ∧ hsame residual BHist.Empty ∧ Cont p residual x := by
  intro readback projection residualRow
  have preXSource : hsame preX sourceTotal :=
    cont_deterministic readback.chosen_readback readback.carried_total_bridge
  have xCarrier : VecSpaceSingletonCarrier x := projection.left
  have pCarrier : VecSpaceSingletonCarrier p := projection.right.left
  have residualEmpty : hsame residual BHist.Empty :=
    cont_right_unit_unique
      (cont_hsame_transport pCarrier (hsame_refl residual) xCarrier residualRow)
  exact And.intro preXSource
    (And.intro xCarrier
      (And.intro pCarrier
        (And.intro residualEmpty (And.intro residualEmpty residualRow))))

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

theorem CondExpProjection_obligation
    {targetTotal sourceTotal chosenPreimage x p residual n : BHist} :
    UnaryHistory sourceTotal ->
      RandomVarTotalReadbackCertificate targetTotal sourceTotal chosenPreimage ->
        HilbertSingletonProjectionWitness x p ->
          VecSpaceSingletonCarrier n ->
            Cont p residual x ->
              VecSpaceSingletonClassifier (HilbertSingletonProjection p) p ∧
                VecSpaceSingletonClassifier (HilbertSingletonProjection x) BHist.Empty ∧
                  RealConstantHistoryClassifier
                    (HilbertSingletonInnerProduct (VecSpaceSingletonSmul x p) n)
                    (BHist.e1 (BHist.e1 BHist.Empty)) ∧
                    UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal ∧
                      Cont p residual x := by
  intro sourceUnary readback projection carrierN residualRow
  have preimageRows :=
    RandomVarTotalReadbackCertificate_total_event_preimage_exactness sourceUnary readback
  have boundaryRows := HilbertSingletonProjection_boundary projection
  have orthogonalRow :=
    HilbertSingletonProjection_orthogonal_zero projection carrierN
  exact And.intro boundaryRows.left
    (And.intro boundaryRows.right.left
      (And.intro orthogonalRow
        (And.intro preimageRows.left
          (And.intro preimageRows.right residualRow))))

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
