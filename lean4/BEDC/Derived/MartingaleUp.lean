import BEDC.Derived.CondExpUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MartingaleUp

open BEDC.Derived.CondExpUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem MartingaleAdaptedSequencePacket_randomvar_boundary
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      UnaryHistory sourceTotal ∧ UnaryHistory chosenPreimage ∧ hsame chosenPreimage sourceTotal ∧
        CondExpCarrierPacket targetTotal sourceTotal chosenPreimage integrable projected residual ∧
          VecSpaceSingletonClassifier projected BHist.Empty := by
  intro packet
  have carrierRows := CondExpCarrier_packet packet.left packet.right.left
  have preimageRows :=
    BEDC.Derived.RandomVarUp.RandomVarTotalReadbackCertificate_total_event_preimage_exactness
      packet.left packet.right.left.left
  exact And.intro packet.left
    (And.intro carrierRows.left
      (And.intro preimageRows.right
        (And.intro packet.right.left carrierRows.right.right.left)))

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

theorem MartingaleAdaptedSequencePacket_public_certificate_row_family
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      SemanticNameCert
        (fun e : BHist =>
          exists s : BHist,
            MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
              projected residual previous filtration s e)
        (fun e : BHist =>
          exists s : BHist,
            MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
              projected residual previous filtration s e)
        (fun e : BHist =>
          exists s : BHist,
            MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
              projected residual previous filtration s e)
        (fun left right : BHist =>
          (exists sl : BHist,
            MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
              projected residual previous filtration sl left) /\
          (exists sr : BHist,
            MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
              projected residual previous filtration sr right) /\
          hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger (Exists.intro stepEndpoint packet)
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
    }

theorem MartingaleAdaptedSequencePacket_namecert_obligation_surface
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      SemanticNameCert
          (fun row : BHist =>
            exists step : BHist,
              MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
                projected residual previous filtration step row)
          (fun row : BHist =>
            exists step : BHist,
              MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
                projected residual previous filtration step row)
          (fun row : BHist =>
            exists step : BHist,
              MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
                projected residual previous filtration step row)
          (fun left right : BHist =>
            (exists sl : BHist,
              MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
                projected residual previous filtration sl left) ∧
              (exists sr : BHist,
                MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable
                  projected residual previous filtration sr right) ∧
                hsame left right) ∧
        Cont integrable filtration stepEndpoint ∧ Cont stepEndpoint previous ledger := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro ledger ?_
          exact Exists.intro stepEndpoint packet
        equiv_refl := by
          intro ledger source
          exact And.intro source (And.intro source (hsame_refl ledger))
        equiv_symm := by
          intro left right classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro left middle right classifiedLM classifiedMR
          exact And.intro classifiedLM.left
            (And.intro classifiedMR.right.left
              (hsame_trans classifiedLM.right.right classifiedMR.right.right))
        carrier_respects_equiv := by
          intro left right classified _source
          exact classified.right.left
      }
      pattern_sound := by
        intro ledger source
        exact source
      ledger_sound := by
        intro ledger source
        exact source
    }
  · exact And.intro packet.right.right.right.left packet.right.right.right.right

theorem MartingaleAdaptedSequencePacket_tower_law_ledger_surface
    {targetTotal sourceTotal chosenPreimage integrable projected residual previous filtration
      stepEndpoint ledger : BHist} :
    MartingaleAdaptedSequencePacket targetTotal sourceTotal chosenPreimage integrable projected
        residual previous filtration stepEndpoint ledger ->
      Cont stepEndpoint previous ledger ∧ hsame ledger (append stepEndpoint previous) := by
  intro packet
  exact And.intro packet.right.right.right.right packet.right.right.right.right

end BEDC.Derived.MartingaleUp
