import BEDC.Derived.ObserverLocalityCellUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverLocalityCellUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverLocalityCellPacket [AskSetup] [PackageSetup]
    (observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  UnaryHistory observerLeft ∧
    UnaryHistory observerRight ∧
      UnaryHistory eventLeft ∧
        UnaryHistory eventRight ∧
          UnaryHistory gapLeft ∧
            UnaryHistory gapRight ∧
              UnaryHistory transport ∧
                UnaryHistory continuation ∧
                  UnaryHistory provenance ∧
                    UnaryHistory nameCert ∧
                      Cont observerLeft eventLeft gapLeft ∧
                        Cont observerRight eventRight gapRight ∧
                          Cont gapLeft gapRight transport ∧
                            Cont transport continuation provenance ∧
                              PkgSig bundle nameCert pkg

theorem ObserverLocalityCellPacket_paired_gap_transport [AskSetup] [PackageSetup]
    {observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert observerLeft' observerRight' eventLeft' eventRight' gapLeft'
      gapRight' transport' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft gapRight
      transport continuation provenance nameCert bundle pkg →
    hsame observerLeft observerLeft' →
    hsame eventLeft eventLeft' →
    hsame observerRight observerRight' →
    hsame eventRight eventRight' →
    Cont observerLeft' eventLeft' gapLeft' →
    Cont observerRight' eventRight' gapRight' →
    Cont gapLeft' gapRight' transport' →
    hsame gapLeft gapLeft' ∧
      hsame gapRight gapRight' ∧
        hsame transport transport' ∧
          UnaryHistory gapLeft' ∧ UnaryHistory gapRight' ∧ UnaryHistory transport' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg
  intro packet sameObserverLeft sameEventLeft sameObserverRight sameEventRight
    gapLeftRow gapRightRow transportRow
  have gapLeftUnary : UnaryHistory gapLeft :=
    packet.right.right.right.right.left
  have gapRightUnary : UnaryHistory gapRight :=
    packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.right.left
  have originalGapLeftRow : Cont observerLeft eventLeft gapLeft :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have originalGapRightRow : Cont observerRight eventRight gapRight :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have originalTransportRow : Cont gapLeft gapRight transport :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameGapLeft : hsame gapLeft gapLeft' :=
    cont_respects_hsame sameObserverLeft sameEventLeft originalGapLeftRow gapLeftRow
  have sameGapRight : hsame gapRight gapRight' :=
    cont_respects_hsame sameObserverRight sameEventRight originalGapRightRow gapRightRow
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameGapLeft sameGapRight originalTransportRow transportRow
  constructor
  · exact sameGapLeft
  · constructor
    · exact sameGapRight
    · constructor
      · exact sameTransport
      · constructor
        · exact unary_transport gapLeftUnary sameGapLeft
        · constructor
          · exact unary_transport gapRightUnary sameGapRight
          · exact unary_transport transportUnary sameTransport

theorem ObserverLocalityCellPacket_classifier_stability_obligation [AskSetup] [PackageSetup]
    {observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert observerLeft' observerRight' eventLeft' eventRight' gapLeft'
      gapRight' transport' continuation' provenance' nameCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft gapRight
        transport continuation provenance nameCert bundle pkg ->
      hsame observerLeft observerLeft' ->
        hsame eventLeft eventLeft' ->
          hsame observerRight observerRight' ->
            hsame eventRight eventRight' ->
              hsame continuation continuation' ->
                hsame nameCert nameCert' ->
                  Cont observerLeft' eventLeft' gapLeft' ->
                    Cont observerRight' eventRight' gapRight' ->
                      Cont gapLeft' gapRight' transport' ->
                        Cont transport' continuation' provenance' ->
                          PkgSig bundle nameCert' pkg ->
                            ObserverLocalityCellPacket observerLeft' observerRight' eventLeft'
                                eventRight' gapLeft' gapRight' transport' continuation'
                                provenance' nameCert' bundle pkg ∧
                              hsame gapLeft gapLeft' ∧ hsame gapRight gapRight' ∧
                                hsame transport transport' ∧ hsame provenance provenance' := by
  intro packet sameObserverLeft sameEventLeft sameObserverRight sameEventRight
    sameContinuation sameNameCert targetGapLeft targetGapRight targetTransport
    targetProvenance targetPkgSig
  have sourceObserverLeftUnary : UnaryHistory observerLeft := packet.left
  have sourceObserverRightUnary : UnaryHistory observerRight := packet.right.left
  have sourceEventLeftUnary : UnaryHistory eventLeft := packet.right.right.left
  have sourceEventRightUnary : UnaryHistory eventRight := packet.right.right.right.left
  have sourceGapLeftUnary : UnaryHistory gapLeft := packet.right.right.right.right.left
  have sourceGapRightUnary : UnaryHistory gapRight := packet.right.right.right.right.right.left
  have sourceTransportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.right.left
  have sourceContinuationUnary : UnaryHistory continuation :=
    packet.right.right.right.right.right.right.right.left
  have sourceProvenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.right.right.right.right.left
  have sourceNameCertUnary : UnaryHistory nameCert :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sourceGapLeft : Cont observerLeft eventLeft gapLeft :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have sourceGapRight : Cont observerRight eventRight gapRight :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have sourceTransport : Cont gapLeft gapRight transport :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sourceProvenance : Cont transport continuation provenance :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have targetObserverLeftUnary : UnaryHistory observerLeft' :=
    unary_transport sourceObserverLeftUnary sameObserverLeft
  have targetObserverRightUnary : UnaryHistory observerRight' :=
    unary_transport sourceObserverRightUnary sameObserverRight
  have targetEventLeftUnary : UnaryHistory eventLeft' :=
    unary_transport sourceEventLeftUnary sameEventLeft
  have targetEventRightUnary : UnaryHistory eventRight' :=
    unary_transport sourceEventRightUnary sameEventRight
  have sameGapLeft : hsame gapLeft gapLeft' :=
    cont_respects_hsame sameObserverLeft sameEventLeft sourceGapLeft targetGapLeft
  have sameGapRight : hsame gapRight gapRight' :=
    cont_respects_hsame sameObserverRight sameEventRight sourceGapRight targetGapRight
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameGapLeft sameGapRight sourceTransport targetTransport
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameContinuation sourceProvenance targetProvenance
  have targetGapLeftUnary : UnaryHistory gapLeft' :=
    unary_transport sourceGapLeftUnary sameGapLeft
  have targetGapRightUnary : UnaryHistory gapRight' :=
    unary_transport sourceGapRightUnary sameGapRight
  have targetTransportUnary : UnaryHistory transport' :=
    unary_transport sourceTransportUnary sameTransport
  have targetContinuationUnary : UnaryHistory continuation' :=
    unary_transport sourceContinuationUnary sameContinuation
  have targetProvenanceUnary : UnaryHistory provenance' :=
    unary_transport sourceProvenanceUnary sameProvenance
  have targetNameCertUnary : UnaryHistory nameCert' :=
    unary_transport sourceNameCertUnary sameNameCert
  exact
    ⟨⟨targetObserverLeftUnary, targetObserverRightUnary, targetEventLeftUnary,
        targetEventRightUnary, targetGapLeftUnary, targetGapRightUnary,
        targetTransportUnary, targetContinuationUnary, targetProvenanceUnary,
        targetNameCertUnary, targetGapLeft, targetGapRight, targetTransport,
        targetProvenance, targetPkgSig⟩,
      sameGapLeft, sameGapRight, sameTransport, sameProvenance⟩

theorem ObserverLocalityCellPacket_scoped_export_surface [AskSetup] [PackageSetup]
    {observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft gapRight
        transport continuation provenance nameCert bundle pkg ->
      Cont transport continuation provenance' ->
        PkgSig bundle nameCert pkg ->
          hsame provenance provenance' ∧ Cont observerLeft eventLeft gapLeft ∧
            Cont observerRight eventRight gapRight ∧ Cont gapLeft gapRight transport ∧
              Cont transport continuation provenance' ∧ PkgSig bundle nameCert pkg := by
  intro packet exportedProvenance exportedPkg
  have sourceProvenance : Cont transport continuation provenance :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl transport) (hsame_refl continuation) sourceProvenance
      exportedProvenance
  constructor
  · exact sameProvenance
  · constructor
    · exact packet.right.right.right.right.right.right.right.right.right.right.left
    · constructor
      · exact packet.right.right.right.right.right.right.right.right.right.right.right.left
      · constructor
        · exact packet.right.right.right.right.right.right.right.right.right.right.right.right.left
        · constructor
          · exact exportedProvenance
          · exact exportedPkg

theorem ObserverLocalityCellPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft gapRight
        transport continuation provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft
              gapRight transport continuation provenance nameCert bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft
              gapRight transport continuation provenance nameCert bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft
              gapRight transport continuation provenance nameCert bundle pkg ∧
            hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert ObserverLocalityCellPacket
  intro packet
  have packetWitness :
      ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft
        gapRight transport continuation provenance nameCert bundle pkg := packet
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert (And.intro packetWitness (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.ObserverLocalityCellUp
