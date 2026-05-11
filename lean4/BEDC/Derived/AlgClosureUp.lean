import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AlgClosureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def AlgClosureCarrierPacket
    (fieldExt polynomial root transport ledger provenance : BHist) : Prop :=
  hsame transport root ∧ Cont polynomial root ledger ∧ Cont fieldExt ledger provenance

theorem AlgClosureCarrierPacket_source_obligation
    {fieldExt polynomial root transport ledger provenance : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance →
      hsame transport root ∧ Cont polynomial root ledger ∧
        Cont fieldExt ledger provenance ∧ hsame provenance (append fieldExt ledger) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right packet.right.right))

theorem AlgClosureCarrierPacket_polynomial_root_classifier_obligation
    {fieldExt fieldExt' polynomial polynomial' root root' transport transport' ledger ledger'
      provenance provenance' : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ->
      hsame fieldExt fieldExt' ->
        hsame polynomial polynomial' ->
          hsame root root' ->
            hsame transport transport' ->
              Cont polynomial' root' ledger' ->
                Cont fieldExt' ledger' provenance' ->
                  AlgClosureCarrierPacket fieldExt' polynomial' root' transport' ledger'
                    provenance' ∧
                    hsame ledger ledger' ∧ hsame provenance provenance' := by
  intro packet sameField samePolynomial sameRoot sameTransport ledgerCont' provenanceCont'
  have sameTransportRoot' : hsame transport' root' :=
    hsame_trans (hsame_symm sameTransport) (hsame_trans packet.left sameRoot)
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame samePolynomial sameRoot packet.right.left ledgerCont'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameField sameLedger packet.right.right provenanceCont'
  exact And.intro
    (And.intro sameTransportRoot' (And.intro ledgerCont' provenanceCont'))
    (And.intro sameLedger sameProvenance)

theorem AlgClosureCarrierPacket_root_witness_transport_coverage
    {fieldExt fieldExt' polynomial polynomial' root root' transport transport' ledger ledger'
      provenance provenance' satisfaction satisfaction' : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ->
      hsame fieldExt fieldExt' ->
        hsame polynomial polynomial' ->
          hsame root root' ->
            hsame transport transport' ->
              Cont polynomial' root' ledger' ->
                Cont fieldExt' ledger' provenance' ->
                  Cont root ledger satisfaction ->
                    Cont root' ledger' satisfaction' ->
                      AlgClosureCarrierPacket fieldExt' polynomial' root' transport' ledger'
                          provenance' ∧
                        hsame ledger ledger' ∧ hsame provenance provenance' ∧
                          hsame satisfaction satisfaction' := by
  intro packet sameField samePolynomial sameRoot sameTransport ledgerCont' provenanceCont'
    satisfactionCont satisfactionCont'
  have transported :=
    AlgClosureCarrierPacket_polynomial_root_classifier_obligation packet sameField samePolynomial
      sameRoot sameTransport ledgerCont' provenanceCont'
  have sameSatisfaction : hsame satisfaction satisfaction' :=
    cont_respects_hsame sameRoot transported.right.left satisfactionCont satisfactionCont'
  exact And.intro transported.left
    (And.intro transported.right.left
      (And.intro transported.right.right sameSatisfaction))

theorem AlgClosureCarrierPacket_ledger_readback_obligation
    {fieldExt polynomial root transport ledger provenance satisfaction : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ->
      Cont root ledger satisfaction ->
        hsame transport root ∧ Cont polynomial root ledger ∧ Cont fieldExt ledger provenance ∧
          Cont root ledger satisfaction ∧ hsame satisfaction (append root ledger) ∧
            hsame provenance (append fieldExt ledger) := by
  intro packet satisfactionRow
  have source :=
    AlgClosureCarrierPacket_source_obligation packet
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro source.right.right.left
          (And.intro satisfactionRow
            (And.intro satisfactionRow source.right.right.right))))

theorem AlgClosureCarrierPacket_downstream_consumer_obligation
    {fieldExt polynomial root transport ledger provenance satisfaction consumer : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ->
      Cont root ledger satisfaction ->
        Cont provenance satisfaction consumer ->
          hsame consumer (append provenance satisfaction) ∧ hsame transport root ∧
            Cont polynomial root ledger ∧ Cont fieldExt ledger provenance ∧
              Cont root ledger satisfaction := by
  intro packet satisfactionRow consumerRow
  exact And.intro consumerRow
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right satisfactionRow)))

theorem AlgClosureCarrierPacket_root_carrier_obligation_surface
    {fieldExt polynomial root transport ledger provenance : BHist} :
    AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ->
      SemanticNameCert
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          hsame ∧
        hsame transport root ∧ Cont polynomial root ledger ∧ Cont fieldExt ledger provenance ∧
          hsame provenance (append fieldExt ledger) := by
  intro packet
  have source := AlgClosureCarrierPacket_source_obligation packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          (fun row : BHist =>
            AlgClosureCarrierPacket fieldExt polynomial root transport ledger provenance ∧
              hsame row provenance)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro packet (hsame_refl provenance))
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        exact And.intro carrierRow.left
          (hsame_trans (hsame_symm sameRows) carrierRow.right)
    }
    pattern_sound := by
      intro _row carrierRow
      exact carrierRow
    ledger_sound := by
      intro _row carrierRow
      exact carrierRow
  }
  exact And.intro cert source

end BEDC.Derived.AlgClosureUp
