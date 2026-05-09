import BEDC.FKernel.Cont

namespace BEDC.Derived.TopgroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem TopGroupRootPublicThreshold_transport
    {G G' T T' product product' inverse inverse' neighborhood neighborhood'
      classifier classifier' provenance provenance' ledger ledger' ledgerOut ledgerOut' : BHist} :
    hsame G G' -> hsame T T' -> hsame product product' -> hsame inverse inverse' ->
      hsame neighborhood neighborhood' -> hsame classifier classifier' -> hsame ledger ledger' ->
        hsame provenance provenance' -> Cont ledger classifier ledgerOut ->
          Cont ledger' classifier' ledgerOut' ->
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
                provenance') := by
  intro sameG sameT sameProduct sameInverse sameNeighborhood sameClassifier sameLedger
    sameProvenance ledgerCont ledgerCont'
  cases sameG
  cases sameT
  cases sameProduct
  cases sameInverse
  cases sameNeighborhood
  cases sameClassifier
  cases sameLedger
  cases sameProvenance
  cases ledgerCont
  cases ledgerCont'
  rfl

theorem TopGroupRootSourceFiber_export_ledger
    {G T product inverse productLedger inverseLedger productOut inverseOut provenance : BHist} :
    Cont G product productLedger -> Cont T inverse inverseLedger ->
      Cont productLedger inverseLedger productOut -> Cont productOut provenance inverseOut ->
        hsame inverseOut (append (append (append G product) (append T inverse)) provenance) := by
  intro productCont inverseCont productLedgerCont provenanceCont
  cases productCont
  cases inverseCont
  cases productLedgerCont
  cases provenanceCont
  rfl

end BEDC.Derived.TopgroupUp
