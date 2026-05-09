import BEDC.FKernel.Cont

namespace BEDC.Derived.AlgClosureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.AlgClosureUp
