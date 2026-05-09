import BEDC.Derived.GroupUp
import BEDC.Derived.TopologyUp.Singleton
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootThresholdPackage
    (group topology product inverse neighborhood ledger provenance : BHist) : Prop :=
  GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory neighborhood ∧
    hsame product (append group topology) ∧ hsame inverse BHist.Empty ∧
      hsame ledger (append product inverse) ∧ hsame provenance ledger

theorem TopGroupRootThreshold_carrier_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
        UnaryHistory topology ∧ UnaryHistory neighborhood ∧ hsame ledger (append product inverse) ∧
          hsame provenance ledger := by
  intro package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro groupUnary
        (And.intro topologyUnary
          (And.intro package.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

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

end BEDC.Derived.TopGroupUp
