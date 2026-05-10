import BEDC.Derived.TopologyUp.PublicCertificate
import BEDC.Derived.TopologyUp.PublicOpenCertificate

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopologyPublicCarriedOpen_standard_bridge (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist}
    (tree : BHistLedgerPublicOpenTree T i U ledger)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist => BHistLedgerPublicOpenTree T i U ledger ∧ T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) ∧
    BHistCarriesOpen T i U ∧
    (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y)) ∧
    TopologyPublicOpenTree T i U := by
  have downstream := BHistLedgerPublicOpenTree_downstream_export_surface T tree source
  have publicTree : TopologyPublicOpenTree T i U :=
    BHistLedgerPublicOpenTree_topology_public_open_tree T tree
  exact And.intro downstream.left
    (And.intro downstream.right.left (And.intro downstream.right.right publicTree))

end BEDC.Derived.TopologyUp
