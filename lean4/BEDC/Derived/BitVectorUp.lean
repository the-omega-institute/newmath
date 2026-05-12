import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BitVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BitVectorPacket [AskSetup] [PackageSetup]
    (length spine ledger provenance packet : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory provenance ∧
    Cont length spine ledger ∧ Cont ledger provenance packet ∧ PkgSig bundle packet pkg

theorem BitVectorPacket_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance packet length' spine' ledger' provenance'
      packet' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorPacket length spine ledger provenance packet bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame provenance provenance' ->
            Cont length' spine' ledger' ->
              Cont ledger' provenance' packet' ->
                PkgSig bundle packet' pkg ->
                  BitVectorPacket length' spine' ledger' provenance' packet' bundle pkg ∧
                    hsame ledger ledger' ∧ hsame packet packet' := by
  intro packetSource sameLength sameSpine sameProvenance ledgerRow' packetRow' packetSig'
  obtain ⟨lengthUnary, spineUnary, provenanceUnary, ledgerRow, packetRow, _packetSig⟩ :=
    packetSource
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed lengthUnary' spineUnary' ledgerRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLength sameSpine ledgerRow ledgerRow'
  have samePacket : hsame packet packet' :=
    cont_respects_hsame sameLedger sameProvenance packetRow packetRow'
  exact And.intro
    (And.intro lengthUnary'
      (And.intro spineUnary'
        (And.intro provenanceUnary' (And.intro ledgerRow' (And.intro packetRow' packetSig')))))
    (And.intro sameLedger samePacket)

end BEDC.Derived.BitVectorUp
