import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireSpacePrefixPacket [AskSetup] [PackageSetup]
    (schedule window classifier ledger provenance restriction endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory classifier ∧
    UnaryHistory ledger ∧ Cont schedule window restriction ∧
      Cont restriction classifier provenance ∧ Cont provenance ledger endpoint ∧
        PkgSig bundle endpoint pkg

theorem BaireSpacePrefixPacket_prefix_cylinder_stability [AskSetup] [PackageSetup]
    {schedule window classifier ledger provenance restriction endpoint schedule' window'
      classifier' ledger' provenance' restriction' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireSpacePrefixPacket schedule window classifier ledger provenance restriction endpoint
        bundle pkg ->
      hsame schedule schedule' -> hsame window window' -> hsame classifier classifier' ->
        hsame ledger ledger' -> Cont schedule' window' restriction' ->
          Cont restriction' classifier' provenance' -> Cont provenance' ledger' endpoint' ->
            PkgSig bundle endpoint' pkg ->
              BaireSpacePrefixPacket schedule' window' classifier' ledger' provenance'
                  restriction' endpoint' bundle pkg ∧
                hsame restriction restriction' ∧ hsame provenance provenance' ∧
                  hsame endpoint endpoint' := by
  intro packet sameSchedule sameWindow sameClassifier sameLedger restrictionRow'
    provenanceRow' endpointRow' pkgSig'
  have restrictionRow : Cont schedule window restriction :=
    packet.right.right.right.right.left
  have provenanceRow : Cont restriction classifier provenance :=
    packet.right.right.right.right.right.left
  have endpointRow : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.left
  have sameRestriction : hsame restriction restriction' :=
    cont_respects_hsame sameSchedule sameWindow restrictionRow restrictionRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRestriction sameClassifier provenanceRow provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLedger endpointRow endpointRow'
  have transported :
      BaireSpacePrefixPacket schedule' window' classifier' ledger' provenance' restriction'
          endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameSchedule,
      unary_transport packet.right.left sameWindow,
      unary_transport packet.right.right.left sameClassifier,
      unary_transport packet.right.right.right.left sameLedger,
      restrictionRow',
      provenanceRow',
      endpointRow',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameRestriction
      (And.intro sameProvenance sameEndpoint))

end BEDC.Derived.BaireSpaceUp
