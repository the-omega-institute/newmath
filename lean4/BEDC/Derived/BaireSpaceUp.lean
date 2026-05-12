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

theorem BaireSpacePrefixPacket_prefix_restriction_composition [AskSetup] [PackageSetup]
    {schedule window classifier ledger provenance restriction endpoint schedule1 window1
      classifier1 ledger1 provenance1 restriction1 endpoint1 schedule2 window2 classifier2
      ledger2 provenance2 restriction2 endpoint2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireSpacePrefixPacket schedule window classifier ledger provenance restriction endpoint
        bundle pkg ->
      hsame schedule schedule1 -> hsame window window1 -> hsame classifier classifier1 ->
        hsame ledger ledger1 -> Cont schedule1 window1 restriction1 ->
          Cont restriction1 classifier1 provenance1 -> Cont provenance1 ledger1 endpoint1 ->
            PkgSig bundle endpoint1 pkg -> hsame schedule1 schedule2 ->
              hsame window1 window2 -> hsame classifier1 classifier2 ->
                hsame ledger1 ledger2 -> Cont schedule2 window2 restriction2 ->
                  Cont restriction2 classifier2 provenance2 ->
                    Cont provenance2 ledger2 endpoint2 -> PkgSig bundle endpoint2 pkg ->
                      BaireSpacePrefixPacket schedule2 window2 classifier2 ledger2 provenance2
                          restriction2 endpoint2 bundle pkg ∧
                        hsame restriction restriction2 ∧ hsame provenance provenance2 ∧
                          hsame endpoint endpoint2 := by
  intro packet sameSchedule01 sameWindow01 sameClassifier01 sameLedger01 restrictionRow1
    provenanceRow1 endpointRow1 pkgSig1 sameSchedule12 sameWindow12 sameClassifier12
    sameLedger12 restrictionRow2 provenanceRow2 endpointRow2 pkgSig2
  have first :=
    BaireSpacePrefixPacket_prefix_cylinder_stability packet sameSchedule01 sameWindow01
      sameClassifier01 sameLedger01 restrictionRow1 provenanceRow1 endpointRow1 pkgSig1
  have second :=
    BaireSpacePrefixPacket_prefix_cylinder_stability first.left sameSchedule12 sameWindow12
      sameClassifier12 sameLedger12 restrictionRow2 provenanceRow2 endpointRow2 pkgSig2
  exact And.intro second.left
    (And.intro (hsame_trans first.right.left second.right.left)
      (And.intro (hsame_trans first.right.right.left second.right.right.left)
        (hsame_trans first.right.right.right second.right.right.right)))

theorem BaireSpacePrefixPacket_real_name_handoff_transport [AskSetup] [PackageSetup]
    {schedule window classifier ledger provenance restriction endpoint schedule' window'
      classifier' ledger' provenance' restriction' endpoint' realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireSpacePrefixPacket schedule window classifier ledger provenance restriction endpoint
        bundle pkg ->
      hsame schedule schedule' -> hsame window window' -> hsame classifier classifier' ->
        hsame ledger ledger' -> Cont schedule' window' restriction' ->
          Cont restriction' classifier' provenance' -> Cont provenance' ledger' endpoint' ->
            Cont endpoint' provenance' realRead -> PkgSig bundle endpoint' pkg ->
              PkgSig bundle realRead pkg ->
                BaireSpacePrefixPacket schedule' window' classifier' ledger' provenance'
                    restriction' endpoint' bundle pkg ∧
                  UnaryHistory realRead ∧ hsame endpoint endpoint' ∧
                    Cont endpoint' provenance' realRead ∧ PkgSig bundle realRead pkg := by
  intro packet sameSchedule sameWindow sameClassifier sameLedger restrictionRow'
    provenanceRow' endpointRow' handoffRow endpointSig readSig
  have stable :=
    BaireSpacePrefixPacket_prefix_cylinder_stability
      (schedule := schedule) (window := window) (classifier := classifier) (ledger := ledger)
      (provenance := provenance) (restriction := restriction) (endpoint := endpoint)
      (schedule' := schedule') (window' := window') (classifier' := classifier')
      (ledger' := ledger') (provenance' := provenance') (restriction' := restriction')
      (endpoint' := endpoint') (bundle := bundle) (pkg := pkg)
      packet sameSchedule sameWindow sameClassifier sameLedger restrictionRow' provenanceRow'
      endpointRow' endpointSig
  have transported :
      BaireSpacePrefixPacket schedule' window' classifier' ledger' provenance' restriction'
          endpoint' bundle pkg :=
    stable.left
  have sameEndpoint : hsame endpoint endpoint' :=
    stable.right.right.right
  have restrictionUnary : UnaryHistory restriction' :=
    unary_cont_closed transported.left transported.right.left restrictionRow'
  have provenanceUnary : UnaryHistory provenance' :=
    unary_cont_closed restrictionUnary transported.right.right.left provenanceRow'
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary transported.right.right.right.left endpointRow'
  have readUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary provenanceUnary handoffRow
  exact And.intro transported
    (And.intro readUnary
      (And.intro sameEndpoint
        (And.intro handoffRow readSig)))

end BEDC.Derived.BaireSpaceUp
