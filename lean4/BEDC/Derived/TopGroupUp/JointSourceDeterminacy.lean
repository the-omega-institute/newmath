import BEDC.Derived.TopGroupUp

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem TopGroupRootPublicThreshold_joint_source_determinacy
    {G G' T T' product product' inverse inverse' neighborhood neighborhood' ledger ledger'
      classifier classifier' provenance provenance' ledgerOut ledgerOut' : BHist} :
    TopGroupRootPublicThresholdPacket G T product inverse neighborhood ledger classifier
        provenance ->
      TopGroupRootPublicThresholdPacket G' T' product' inverse' neighborhood' ledger'
        classifier' provenance' ->
        hsame G G' -> hsame T T' -> hsame product product' -> hsame inverse inverse' ->
          hsame neighborhood neighborhood' -> hsame classifier classifier' ->
            hsame ledger ledger' -> hsame provenance provenance' ->
              Cont ledger classifier ledgerOut -> Cont ledger' classifier' ledgerOut' ->
                hsame
                    (append
                      (append
                        (append
                          (append
                            (append
                              (append G T)
                              product)
                            inverse)
                          neighborhood)
                        ledgerOut)
                      provenance)
                    (append
                      (append
                        (append
                          (append
                            (append
                              (append G' T')
                              product')
                            inverse')
                          neighborhood')
                        ledgerOut')
                      provenance') ∧
                  hsame provenance BHist.Empty ∧ hsame provenance' BHist.Empty := by
  intro packet packet' sameG sameT sameProduct sameInverse sameNeighborhood sameClassifier
    sameLedger sameProvenance ledgerCont ledgerCont'
  have surface :=
    TopGroupRootPublicThreshold_transport
      (G := G) (G' := G') (T := T) (T' := T') (product := product)
      (product' := product') (inverse := inverse) (inverse' := inverse')
      (neighborhood := neighborhood) (neighborhood' := neighborhood')
      (classifier := classifier) (classifier' := classifier') (provenance := provenance)
      (provenance' := provenance') (ledger := ledger) (ledger' := ledger')
      (ledgerOut := ledgerOut) (ledgerOut' := ledgerOut') sameG sameT sameProduct sameInverse
      sameNeighborhood sameClassifier sameLedger sameProvenance ledgerCont ledgerCont'
  exact And.intro surface
    (And.intro packet.right.right.right.right.right packet'.right.right.right.right.right)

end BEDC.Derived.TopGroupUp
