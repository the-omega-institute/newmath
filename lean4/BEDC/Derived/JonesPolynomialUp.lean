import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont

namespace BEDC.Derived.JonesPolynomialUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.JonesPolynomialUp
