import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KnotUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KnotDiagramPacket [AskSetup] [PackageSetup]
    (sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sone ∧ UnaryHistory ambient ∧ UnaryHistory diagram ∧ UnaryHistory trace ∧
    UnaryHistory homotopy ∧ UnaryHistory endpoint0 ∧ UnaryHistory endpoint1 ∧
      Cont sone ambient provenance ∧ Cont endpoint0 endpoint1 ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem KnotDiagramPacket_sone_source_boundary [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        hsame provenance (append sone ambient) ∧ hsame ledger (append endpoint0 endpoint1) ∧
          hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have soneUnary : UnaryHistory sone :=
    packet.left
  have ambientUnary : UnaryHistory ambient :=
    packet.right.left
  have endpoint0Unary : UnaryHistory endpoint0 :=
    packet.right.right.right.right.right.left
  have endpoint1Unary : UnaryHistory endpoint1 :=
    packet.right.right.right.right.right.right.left
  have provenanceCont : Cont sone ambient provenance :=
    packet.right.right.right.right.right.right.right.left
  have ledgerCont : Cont endpoint0 endpoint1 ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed soneUnary ambientUnary provenanceCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpoint0Unary endpoint1Unary ledgerCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary endpointCont
  exact And.intro provenanceUnary
    (And.intro ledgerUnary
      (And.intro endpointUnary
        (And.intro provenanceCont
          (And.intro ledgerCont
            (And.intro endpointCont
              packet.right.right.right.right.right.right.right.right.right.right)))))

theorem KnotDiagramPacket_projection_stability_obligation [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint
      sone' ambient' homotopy' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      hsame sone sone' ->
        hsame ambient ambient' ->
          hsame homotopy homotopy' ->
            Cont sone' ambient' provenance' ->
              Cont provenance' ledger endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  KnotDiagramPacket sone' ambient' diagram trace homotopy' endpoint0 endpoint1
                      provenance' ledger endpoint' bundle pkg ∧
                    hsame endpoint endpoint' := by
  intro packet sameSone sameAmbient sameHomotopy provenanceRow endpointRow endpointPkg
  have soneUnary : UnaryHistory sone' :=
    unary_transport packet.left sameSone
  have ambientUnary : UnaryHistory ambient' :=
    unary_transport packet.right.left sameAmbient
  have homotopyUnary : UnaryHistory homotopy' :=
    unary_transport packet.right.right.right.right.left sameHomotopy
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSone sameAmbient
      packet.right.right.right.right.right.right.right.left provenanceRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance (hsame_refl ledger)
      packet.right.right.right.right.right.right.right.right.right.left endpointRow
  exact And.intro
    (And.intro soneUnary
      (And.intro ambientUnary
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro homotopyUnary
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro provenanceRow
                    (And.intro packet.right.right.right.right.right.right.right.right.left
                      (And.intro endpointRow endpointPkg))))))))))
    sameEndpoint

theorem KnotDiagramPacket_endpoint_source_exhaustion [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory endpoint0 ∧ UnaryHistory endpoint1 ∧ UnaryHistory provenance ∧
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont sone ambient provenance ∧
          Cont endpoint0 endpoint1 ledger ∧ Cont provenance ledger endpoint ∧
            hsame endpoint (append (append sone ambient) (append endpoint0 endpoint1)) ∧
              PkgSig bundle endpoint pkg := by
  intro packet
  have endpoint0Unary : UnaryHistory endpoint0 :=
    packet.right.right.right.right.right.left
  have endpoint1Unary : UnaryHistory endpoint1 :=
    packet.right.right.right.right.right.right.left
  have provenanceCont : Cont sone ambient provenance :=
    packet.right.right.right.right.right.right.right.left
  have ledgerCont : Cont endpoint0 endpoint1 ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have packetRows :=
    KnotDiagramPacket_sone_source_boundary packet
  have endpointReadback :
      hsame endpoint (append (append sone ambient) (append endpoint0 endpoint1)) := by
    cases provenanceCont
    cases ledgerCont
    exact endpointCont
  exact And.intro endpoint0Unary
    (And.intro endpoint1Unary
      (And.intro packetRows.left
        (And.intro packetRows.right.left
          (And.intro packetRows.right.right.left
            (And.intro provenanceCont
              (And.intro ledgerCont
                (And.intro endpointCont
                  (And.intro endpointReadback
                    packetRows.right.right.right.right.right.right))))))))

theorem KnotDiagramPacket_homotopy_ledger_boundary [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory diagram ∧ UnaryHistory trace ∧ UnaryHistory homotopy ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ Cont endpoint0 endpoint1 ledger ∧
          hsame ledger (append endpoint0 endpoint1) ∧ hsame endpoint (append provenance ledger) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have diagramUnary : UnaryHistory diagram := packet.right.right.left
  have traceUnary : UnaryHistory trace := packet.right.right.right.left
  have homotopyUnary : UnaryHistory homotopy := packet.right.right.right.right.left
  have soneUnary : UnaryHistory sone := packet.left
  have ambientUnary : UnaryHistory ambient := packet.right.left
  have endpoint0Unary : UnaryHistory endpoint0 :=
    packet.right.right.right.right.right.left
  have endpoint1Unary : UnaryHistory endpoint1 :=
    packet.right.right.right.right.right.right.left
  have provenanceCont : Cont sone ambient provenance :=
    packet.right.right.right.right.right.right.right.left
  have ledgerCont : Cont endpoint0 endpoint1 ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed soneUnary ambientUnary provenanceCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpoint0Unary endpoint1Unary ledgerCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary endpointCont
  exact And.intro diagramUnary
    (And.intro traceUnary
      (And.intro homotopyUnary
        (And.intro ledgerUnary
          (And.intro endpointUnary
            (And.intro ledgerCont
              (And.intro ledgerCont
                (And.intro endpointCont
                  packet.right.right.right.right.right.right.right.right.right.right)))))))

theorem KnotReidemeisterLedgerClassifier_empty_reflexive [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      Cont endpoint BHist.Empty endpoint ->
        UnaryHistory endpoint ∧ hsame endpoint endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet emptyLedger
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  have endpointSame : hsame endpoint endpoint :=
    cont_deterministic emptyLedger (cont_right_unit endpoint)
  exact And.intro sourceRows.right.right.left
    (And.intro endpointSame sourceRows.right.right.right.right.right.right)

theorem KnotReidemeisterLedgerClassifier_composition_closure [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint endpoint'
      joined final : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory endpoint' ->
        Cont endpoint endpoint' joined ->
          Cont joined endpoint' final ->
            PkgSig bundle final pkg ->
              UnaryHistory joined ∧ UnaryHistory final ∧
                hsame joined (append endpoint endpoint') ∧
                  hsame final (append joined endpoint') ∧ PkgSig bundle final pkg := by
  intro packet endpointUnary' endpointJoin joinedEndpoint finalPkg
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  have endpointUnary : UnaryHistory endpoint :=
    sourceRows.right.right.left
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed endpointUnary endpointUnary' endpointJoin
  have finalUnary : UnaryHistory final :=
    unary_cont_closed joinedUnary endpointUnary' joinedEndpoint
  exact And.intro joinedUnary
    (And.intro finalUnary
      (And.intro endpointJoin
        (And.intro joinedEndpoint finalPkg)))

theorem KnotDiagramPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory sone ∧ UnaryHistory ambient ∧ UnaryHistory diagram ∧ UnaryHistory trace ∧
        UnaryHistory homotopy ∧ UnaryHistory endpoint0 ∧ UnaryHistory endpoint1 ∧
          UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            Cont sone ambient provenance ∧ Cont endpoint0 endpoint1 ledger ∧
              Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  constructor
  · exact packet.left
  · constructor
    · exact packet.right.left
    · constructor
      · exact packet.right.right.left
      · constructor
        · exact packet.right.right.right.left
        · constructor
          · exact packet.right.right.right.right.left
          · constructor
            · exact packet.right.right.right.right.right.left
            · constructor
              · exact packet.right.right.right.right.right.right.left
              · constructor
                · exact sourceRows.left
                · constructor
                  · exact sourceRows.right.left
                  · constructor
                    · exact sourceRows.right.right.left
                    · constructor
                      · exact packet.right.right.right.right.right.right.right.left
                      · constructor
                        · exact packet.right.right.right.right.right.right.right.right.left
                        · constructor
                          · exact packet.right.right.right.right.right.right.right.right.right.left
                          · exact packet.right.right.right.right.right.right.right.right.right.right

theorem KnotReidemeisterLedgerClassifier_ledger_completeness [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance
                ledger e bundle pkg ∧ hsame row e)
          hsame ∧
        UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
          Cont endpoint0 endpoint1 ledger ∧ Cont provenance ledger endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  let Carrier : BHist -> Prop :=
    fun row : BHist =>
      exists e : BHist,
        KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
          e bundle pkg ∧ hsame row e
  have core : NameCert Carrier hsame := {
    carrier_inhabited := Exists.intro endpoint
      (show Carrier endpoint from Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
    equiv_refl := by
      intro row _rowCarrier
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro row row' sameRows rowCarrier
      cases rowCarrier with
      | intro e data =>
          exact Exists.intro e
            (And.intro data.left (hsame_trans (hsame_symm sameRows) data.right))
  }
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := core
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  exact And.intro cert
    (And.intro sourceRows.left
      (And.intro sourceRows.right.left
        (And.intro sourceRows.right.right.left
          (And.intro sourceRows.right.right.right.right.left
            (And.intro sourceRows.right.right.right.right.right.left
              sourceRows.right.right.right.right.right.right)))))

theorem KnotDiagramPacket_ambient_isotopy_ledger_exactness [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory sone ∧ UnaryHistory ambient ∧ UnaryHistory endpoint0 ∧
        UnaryHistory endpoint1 ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ hsame provenance (append sone ambient) ∧
            hsame ledger (append endpoint0 endpoint1) ∧
              hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.left
          (And.intro sourceRows.left
            (And.intro sourceRows.right.left
                (And.intro sourceRows.right.right.left
                  (And.intro sourceRows.right.right.right.left
                    (And.intro sourceRows.right.right.right.right.left
                      (And.intro sourceRows.right.right.right.right.right.left
                        sourceRows.right.right.right.right.right.right)))))))))

theorem KnotReidemeisterLedgerClassifier_reversal_symmetry [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint
      reverseLedger reverseEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      Cont endpoint1 endpoint0 reverseLedger ->
        Cont provenance reverseLedger reverseEndpoint ->
          PkgSig bundle reverseEndpoint pkg ->
            UnaryHistory reverseLedger ∧ UnaryHistory reverseEndpoint ∧
              hsame reverseLedger (append endpoint1 endpoint0) ∧
                hsame reverseEndpoint (append provenance reverseLedger) ∧
                  PkgSig bundle reverseEndpoint pkg := by
  intro packet reverseLedgerRow reverseEndpointRow reversePkg
  have sourceRows :=
    KnotDiagramPacket_sone_source_boundary packet
  have reverseLedgerUnary : UnaryHistory reverseLedger :=
    unary_cont_closed packet.right.right.right.right.right.right.left
      packet.right.right.right.right.right.left reverseLedgerRow
  have reverseEndpointUnary : UnaryHistory reverseEndpoint :=
    unary_cont_closed sourceRows.left reverseLedgerUnary reverseEndpointRow
  exact And.intro reverseLedgerUnary
    (And.intro reverseEndpointUnary
      (And.intro reverseLedgerRow
        (And.intro reverseEndpointRow reversePkg)))

end BEDC.Derived.KnotUp
