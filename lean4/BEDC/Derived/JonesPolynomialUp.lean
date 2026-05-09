import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.JonesPolynomialUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive JonesSkeinBoundaryTag where
  | diagram
  | positive
  | negative
  | smoothing
  | endpoint

def JonesSkeinLedgerPacket
    (diagram positive negative smoothing endpoint provenance contLedger : BHist)
    (skeinLedger : ProbeBundle JonesSkeinBoundaryTag) : Prop :=
  InBundle JonesSkeinBoundaryTag.diagram skeinLedger ∧
    InBundle JonesSkeinBoundaryTag.positive skeinLedger ∧
      InBundle JonesSkeinBoundaryTag.negative skeinLedger ∧
        InBundle JonesSkeinBoundaryTag.smoothing skeinLedger ∧
          InBundle JonesSkeinBoundaryTag.endpoint skeinLedger ∧
            Cont positive negative smoothing ∧ Cont diagram endpoint provenance ∧
              Cont provenance endpoint contLedger

theorem JonesSkeinLedgerPacket_reidemeister_transport
    {diagram diagram' positive negative smoothing endpoint endpoint' provenance provenance'
      contLedger contLedger' : BHist} {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
      skeinLedger ->
      hsame diagram diagram' ->
        hsame endpoint endpoint' ->
          Cont diagram' endpoint' provenance' ->
            Cont provenance' endpoint' contLedger' ->
              JonesSkeinLedgerPacket diagram' positive negative smoothing endpoint' provenance'
                  contLedger' skeinLedger ∧
                hsame provenance provenance' ∧ hsame contLedger contLedger' := by
  intro packet sameDiagram sameEndpoint transportedProvenance transportedLedger
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameDiagram sameEndpoint packet.right.right.right.right.right.right.left
      transportedProvenance
  have sameLedger : hsame contLedger contLedger' :=
    cont_respects_hsame sameProvenance sameEndpoint packet.right.right.right.right.right.right.right
      transportedLedger
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro transportedProvenance transportedLedger)))))))
    (And.intro sameProvenance sameLedger)

theorem JonesSkeinLedgerPacket_obligation_surface
    {diagram positive negative smoothing endpoint provenance contLedger : BHist}
    {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
      skeinLedger ->
      InBundle JonesSkeinBoundaryTag.diagram skeinLedger ∧
        InBundle JonesSkeinBoundaryTag.positive skeinLedger ∧
          InBundle JonesSkeinBoundaryTag.negative skeinLedger ∧
            InBundle JonesSkeinBoundaryTag.smoothing skeinLedger ∧
              InBundle JonesSkeinBoundaryTag.endpoint skeinLedger ∧
                Cont positive negative smoothing ∧ Cont diagram endpoint provenance ∧
                  Cont provenance endpoint contLedger ∧
                    hsame contLedger (append provenance endpoint) := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.right
                    packet.right.right.right.right.right.right.right)))))))

theorem JonesSkeinLedgerPacket_local_skein_window_composition
    {diagram positive negative smoothing endpoint provenance contLedger : BHist}
    {left right : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger left ->
      JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger right ->
        JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
            (bundleAppend left right) ∧
          InBundle JonesSkeinBoundaryTag.positive (bundleAppend left right) ∧
            InBundle JonesSkeinBoundaryTag.negative (bundleAppend left right) ∧
              InBundle JonesSkeinBoundaryTag.smoothing (bundleAppend left right) := by
  intro leftPacket _rightPacket
  have diagramRow :
      InBundle JonesSkeinBoundaryTag.diagram (bundleAppend left right) :=
    Iff.mpr inBundle_bundleAppend_iff (Or.inl leftPacket.left)
  have positiveRow :
      InBundle JonesSkeinBoundaryTag.positive (bundleAppend left right) :=
    Iff.mpr inBundle_bundleAppend_iff (Or.inl leftPacket.right.left)
  have negativeRow :
      InBundle JonesSkeinBoundaryTag.negative (bundleAppend left right) :=
    Iff.mpr inBundle_bundleAppend_iff (Or.inl leftPacket.right.right.left)
  have smoothingRow :
      InBundle JonesSkeinBoundaryTag.smoothing (bundleAppend left right) :=
    Iff.mpr inBundle_bundleAppend_iff (Or.inl leftPacket.right.right.right.left)
  have endpointRow :
      InBundle JonesSkeinBoundaryTag.endpoint (bundleAppend left right) :=
    Iff.mpr inBundle_bundleAppend_iff (Or.inl leftPacket.right.right.right.right.left)
  have appendedPacket :
      JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
        (bundleAppend left right) :=
    And.intro diagramRow
      (And.intro positiveRow
        (And.intro negativeRow
          (And.intro smoothingRow
            (And.intro endpointRow
              (And.intro leftPacket.right.right.right.right.right.left
                (And.intro leftPacket.right.right.right.right.right.right.left
                  leftPacket.right.right.right.right.right.right.right))))))
  exact And.intro appendedPacket
    (And.intro positiveRow
      (And.intro negativeRow smoothingRow))

theorem JonesSkeinLedgerPacket_skein_boundary_no_confusion
    {diagram positive negative smoothing endpoint provenance contLedger : BHist}
    {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
        skeinLedger ->
      JonesSkeinBoundaryTag.positive ≠ JonesSkeinBoundaryTag.negative ∧
        JonesSkeinBoundaryTag.positive ≠ JonesSkeinBoundaryTag.smoothing ∧
          JonesSkeinBoundaryTag.negative ≠ JonesSkeinBoundaryTag.smoothing ∧
            InBundle JonesSkeinBoundaryTag.positive skeinLedger ∧
              InBundle JonesSkeinBoundaryTag.negative skeinLedger ∧
                InBundle JonesSkeinBoundaryTag.smoothing skeinLedger := by
  intro packet
  have positive_ne_negative :
      JonesSkeinBoundaryTag.positive ≠ JonesSkeinBoundaryTag.negative := by
    intro same
    cases same
  have positive_ne_smoothing :
      JonesSkeinBoundaryTag.positive ≠ JonesSkeinBoundaryTag.smoothing := by
    intro same
    cases same
  have negative_ne_smoothing :
      JonesSkeinBoundaryTag.negative ≠ JonesSkeinBoundaryTag.smoothing := by
    intro same
    cases same
  exact And.intro positive_ne_negative
    (And.intro positive_ne_smoothing
      (And.intro negative_ne_smoothing
        (And.intro packet.right.left
          (And.intro packet.right.right.left packet.right.right.right.left))))

theorem JonesSkeinLedgerPacket_skein_classifier_determinacy
    {diagram positive negative smoothing endpoint provenance contLedger endpoint' provenance'
      contLedger' : BHist} {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
        skeinLedger ->
      hsame endpoint endpoint' ->
        Cont diagram endpoint' provenance' ->
          Cont provenance' endpoint' contLedger' ->
            SemanticNameCert (fun row : BHist => hsame row endpoint')
              (fun row : BHist => hsame row endpoint')
              (fun row : BHist => hsame row endpoint') hsame ∧
            hsame provenance provenance' ∧ hsame contLedger contLedger' ∧
              hsame contLedger' (append provenance' endpoint') ∧
                InBundle JonesSkeinBoundaryTag.endpoint skeinLedger := by
  intro packet sameEndpoint transportedProvenance transportedLedger
  have transported :=
    JonesSkeinLedgerPacket_reidemeister_transport packet (hsame_refl diagram) sameEndpoint
      transportedProvenance transportedLedger
  have endpointSelf : hsame endpoint' endpoint' :=
    hsame_refl endpoint'
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint')
        (fun row : BHist => hsame row endpoint')
        (fun row : BHist => hsame row endpoint') hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint' endpointSelf
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other target sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other sameRO source
        exact hsame_trans (hsame_symm sameRO) source
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro transported.right.left
      (And.intro transported.right.right
        (And.intro transportedLedger
          transported.left.right.right.right.right.left)))

theorem JonesSkeinLedgerPacket_endpoint_classifier_exhaustion
    {diagram positive negative smoothing endpoint provenance contLedger : BHist}
    {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
        skeinLedger ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        InBundle JonesSkeinBoundaryTag.diagram skeinLedger ∧
          InBundle JonesSkeinBoundaryTag.positive skeinLedger ∧
            InBundle JonesSkeinBoundaryTag.negative skeinLedger ∧
              InBundle JonesSkeinBoundaryTag.smoothing skeinLedger ∧
                InBundle JonesSkeinBoundaryTag.endpoint skeinLedger ∧
                  Cont positive negative smoothing ∧ Cont diagram endpoint provenance ∧
                    Cont provenance endpoint contLedger ∧
                      hsame contLedger (append provenance endpoint) := by
  intro packet
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other target sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other sameRO source
        exact hsame_trans (hsame_symm sameRO) source
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.right
                    packet.right.right.right.right.right.right.right))))))))

theorem JonesSkeinLedgerPacket_namecert_obligation_surface
    {diagram positive negative smoothing endpoint provenance contLedger : BHist}
    {skeinLedger : ProbeBundle JonesSkeinBoundaryTag} :
    JonesSkeinLedgerPacket diagram positive negative smoothing endpoint provenance contLedger
        skeinLedger ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        InBundle JonesSkeinBoundaryTag.diagram skeinLedger ∧
          InBundle JonesSkeinBoundaryTag.positive skeinLedger ∧
            InBundle JonesSkeinBoundaryTag.negative skeinLedger ∧
              InBundle JonesSkeinBoundaryTag.smoothing skeinLedger ∧
                InBundle JonesSkeinBoundaryTag.endpoint skeinLedger ∧
                  Cont positive negative smoothing ∧ Cont diagram endpoint provenance ∧
                    Cont provenance endpoint contLedger := by
  intro packet
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other same
        exact hsame_symm same
      equiv_trans := by
        intro row other target sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro row other sameRO source
        exact hsame_trans (hsame_symm sameRO) source
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  packet.right.right.right.right.right.right.right)))))))

end BEDC.Derived.JonesPolynomialUp
