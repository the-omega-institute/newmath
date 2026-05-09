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

def TopGroupRootPublicThresholdPacket
    (groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist) : Prop :=
  GroupSingletonCarrier groupSource ∧ TopologySingletonCarrier topologySource ∧
    Cont product inverse ledger ∧ hsame neighbourhood BHist.Empty ∧
      hsame classifier ledger ∧ hsame provenance BHist.Empty

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

theorem TopGroupRootThreshold_product_inverse_empty_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product BHist.Empty ∧ hsame inverse BHist.Empty ∧ hsame ledger BHist.Empty ∧
        hsame provenance BHist.Empty := by
  intro package
  have productEmpty : hsame product BHist.Empty :=
    hsame_trans package.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro package.left package.right.left))
  have ledgerEmpty : hsame ledger BHist.Empty :=
    hsame_trans package.right.right.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro productEmpty package.right.right.right.right.left))
  exact And.intro productEmpty
    (And.intro package.right.right.right.right.left
      (And.intro ledgerEmpty
        (hsame_trans package.right.right.right.right.right.right ledgerEmpty)))

theorem TopGroupRootThreshold_classifier_ledger_transport_packet
    {group topology product inverse neighborhood ledger provenance ledger' provenance' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame ledger' ledger ->
        hsame provenance' provenance ->
          hsame ledger' (append product inverse) ∧ hsame provenance' ledger' ∧
            TopGroupRootThresholdPackage group topology product inverse neighborhood ledger'
              provenance' := by
  intro package sameLedger sameProvenance
  have ledgerEndpoint : hsame ledger' (append product inverse) :=
    hsame_trans sameLedger package.right.right.right.right.right.left
  have provenanceEndpoint : hsame provenance' ledger' :=
    hsame_trans sameProvenance
      (hsame_trans package.right.right.right.right.right.right (hsame_symm sameLedger))
  exact And.intro ledgerEndpoint
    (And.intro provenanceEndpoint
      (And.intro package.left
        (And.intro package.right.left
          (And.intro package.right.right.left
              (And.intro package.right.right.right.left
                (And.intro package.right.right.right.right.left
                  (And.intro ledgerEndpoint provenanceEndpoint)))))))

theorem TopGroupRootThresholdPackage_continuity_ledger_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product inverse ledger ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
        hsame provenance ledger := by
  intro package
  have rows := TopGroupRootThreshold_carrier_scope package
  have productUnary : UnaryHistory product :=
    unary_transport (unary_append_closed rows.right.right.left rows.right.right.right.left)
      (hsame_symm package.right.right.right.left)
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerCont : Cont product inverse ledger :=
    package.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed productUnary inverseUnary ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport ledgerUnary (hsame_symm rows.right.right.right.right.right.right)
  exact And.intro ledgerCont
    (And.intro ledgerUnary
      (And.intro provenanceUnary rows.right.right.right.right.right.right))

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
