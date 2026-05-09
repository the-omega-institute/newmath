import BEDC.Derived.DeRhamUp

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem DeRhamRootCarrier_obligation {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty ∧
        SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame := by
  intro packet
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet
  have cert : SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame :=
    DeRhamBoundary_semanticNameCert boundaryRows.right.left
  exact And.intro boundaryRows.right.left
    (And.intro boundaryRows.left (And.intro boundaryRows.right.right cert))

theorem DeRhamRootCocycleLedger_threshold
    {d : BHist -> BHist} {omega eta theta zero provenance bridge consumer : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      Cont bridge zero consumer ->
        hsame (d eta) BHist.Empty ∧
          SemanticNameCert (fun h : BHist => hsame (d h) BHist.Empty)
            (fun h : BHist => hsame (d h) BHist.Empty)
            (fun h : BHist => hsame (d h) BHist.Empty) hsame ∧
          hsame consumer (append bridge zero) ∧ Cont provenance theta bridge := by
  intro packet consumerRow
  have cocycleRows := DeRhamDoubleExteriorPacket_cohomology_cocycle_readback packet.left
  exact And.intro cocycleRows.left
    (And.intro cocycleRows.right (And.intro consumerRow packet.right))

end BEDC.Derived.DeRhamUp
