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

def BitVectorSourcePacket [AskSetup] [PackageSetup]
    (length spine ledger provenance lengthSpineRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
    Cont length spine lengthSpineRoute ∧ Cont lengthSpineRoute ledger provenance ∧
      PkgSig bundle provenance pkg

theorem BitVectorSourcePacket_carrier_stability [AskSetup] [PackageSetup]
    {length spine ledger provenance lengthSpineRoute length' spine' ledger' provenance'
      lengthSpineRoute' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BitVectorSourcePacket length spine ledger provenance lengthSpineRoute bundle pkg ->
      hsame length length' -> hsame spine spine' -> hsame ledger ledger' ->
        Cont length' spine' lengthSpineRoute' ->
          Cont lengthSpineRoute' ledger' provenance' ->
            PkgSig bundle provenance' pkg ->
              BitVectorSourcePacket length' spine' ledger' provenance' lengthSpineRoute'
                  bundle pkg ∧
                hsame lengthSpineRoute lengthSpineRoute' ∧ hsame provenance provenance' := by
  intro packet sameLength sameSpine sameLedger lengthSpineRow' provenanceRow' pkgSig'
  have lengthSpineRow : Cont length spine lengthSpineRoute :=
    packet.right.right.right.right.left
  have provenanceRow : Cont lengthSpineRoute ledger provenance :=
    packet.right.right.right.right.right.left
  have sameLengthSpineRoute : hsame lengthSpineRoute lengthSpineRoute' :=
    cont_respects_hsame sameLength sameSpine lengthSpineRow lengthSpineRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLengthSpineRoute sameLedger provenanceRow provenanceRow'
  have transported :
      BitVectorSourcePacket length' spine' ledger' provenance' lengthSpineRoute' bundle pkg :=
    ⟨unary_transport packet.left sameLength,
      unary_transport packet.right.left sameSpine,
      unary_transport packet.right.right.left sameLedger,
      unary_transport packet.right.right.right.left sameProvenance,
      lengthSpineRow',
      provenanceRow',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameLengthSpineRoute sameProvenance)

end BEDC.Derived.BitVectorUp
