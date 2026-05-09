import BEDC.Derived.GroupUp
import BEDC.Derived.TopologyUp.Singleton
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem TopGroupRootThresholdPackage_source_coupled_continuity_boundary
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory product ∧
        UnaryHistory inverse ∧ UnaryHistory neighborhood ∧ UnaryHistory ledger ∧
          hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package
  have scope := TopGroupRootThreshold_carrier_scope package
  have productUnaryRaw : UnaryHistory (append group topology) :=
    unary_append_closed scope.right.right.left scope.right.right.right.left
  have productUnary : UnaryHistory product :=
    unary_transport productUnaryRaw (hsame_symm package.right.right.right.left)
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerUnaryRaw : UnaryHistory (append product inverse) :=
    unary_append_closed productUnary inverseUnary
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport ledgerUnaryRaw (hsame_symm package.right.right.right.right.right.left)
  exact And.intro scope.left
    (And.intro scope.right.left
      (And.intro productUnary
        (And.intro inverseUnary
          (And.intro scope.right.right.right.right.left
            (And.intro ledgerUnary
              (And.intro scope.right.right.right.right.right.left
                scope.right.right.right.right.right.right))))))

theorem TopGroupRootThresholdPackage_multiplication_continuity_carrier
    {group topology product inverse neighborhood ledger provenance productLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory product ∧
          UnaryHistory neighborhood ∧ UnaryHistory productLedger ∧
            Cont product neighborhood productLedger ∧ hsame productLedger (append product neighborhood) ∧
              hsame provenance ledger := by
  intro package productLedgerCont
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  exact
    ⟨boundary.left, boundary.right.left, boundary.right.right.left,
      boundary.right.right.right.right.left,
      unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
        productLedgerCont,
      productLedgerCont, productLedgerCont, boundary.right.right.right.right.right.right.right⟩

theorem TopGroupRootThresholdPackage_operation_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      exists productLedger inverseLedger : BHist,
        Cont product neighborhood productLedger ∧ Cont inverse neighborhood inverseLedger ∧
          UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧ Cont product inverse ledger ∧
            hsame ledger (append product inverse) := by
  intro package
  let productLedger := append product neighborhood
  let inverseLedger := append inverse neighborhood
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productCont : Cont product neighborhood productLedger := by
    rfl
  have inverseCont : Cont inverse neighborhood inverseLedger := by
    rfl
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed rows.right.right.left rows.right.right.right.right.left productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed rows.right.right.right.left rows.right.right.right.right.left inverseCont
  exact Exists.intro productLedger
    (Exists.intro inverseLedger
      (And.intro productCont
        (And.intro inverseCont
          (And.intro productLedgerUnary
            (And.intro inverseLedgerUnary
              (And.intro package.right.right.right.right.right.left
                package.right.right.right.right.right.left))))))

theorem TopGroupRootThresholdPackage_shared_source_rows
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group topology product ∧ Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
        UnaryHistory ledger ∧ UnaryHistory provenance := by
  intro package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have productCont : Cont group topology product := by
    exact package.right.right.right.left
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerCont : Cont product inverse ledger := by
    exact package.right.right.right.right.right.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed groupUnary topologyUnary productCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed productUnary inverseUnary ledgerCont
  have provenanceCont : Cont ledger BHist.Empty provenance := by
    cases package.right.right.right.right.right.right
    exact cont_right_unit ledger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary unary_empty provenanceCont
  exact And.intro productCont
    (And.intro ledgerCont
      (And.intro provenanceCont (And.intro ledgerUnary provenanceUnary)))

theorem TopGroupRootSourceFiber_export_carrier
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ Cont group topology product ∧
        Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
          UnaryHistory provenance := by
  intro package
  have rows := TopGroupRootThresholdPackage_shared_source_rows package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro rows.left
        (And.intro rows.right.left
          (And.intro rows.right.right.left rows.right.right.right.right))))

theorem TopGroupRootThresholdPackage_consumer_exhaustion
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧ Cont product inverse ledger ∧
              hsame provenance ledger := by
  intro package productLedgerCont inverseLedgerCont
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left
      productLedgerCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseLedgerCont
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro productLedgerUnary
        (And.intro inverseLedgerUnary
          (And.intro package.right.right.right.right.right.left
            package.right.right.right.right.right.right))))

theorem TopGroupRootThresholdPackage_export_boundary_certificate
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame ∧ hsame provenance BHist.Empty := by
  intro package
  have groupEmpty : hsame group BHist.Empty := package.left
  have topologyEmpty : hsame topology BHist.Empty := package.right.left
  have productEmpty : hsame product BHist.Empty := by
    have productAppend : hsame product (append group topology) := package.right.right.right.left
    have appendEmpty : hsame (append group topology) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro groupEmpty topologyEmpty)
    exact hsame_trans productAppend appendEmpty
  have inverseEmpty : hsame inverse BHist.Empty := package.right.right.right.right.left
  have ledgerEmpty : hsame ledger BHist.Empty := by
    have ledgerAppend : hsame ledger (append product inverse) :=
      package.right.right.right.right.right.left
    have appendEmpty : hsame (append product inverse) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro productEmpty inverseEmpty)
    exact hsame_trans ledgerAppend appendEmpty
  have provenanceEmpty : hsame provenance BHist.Empty :=
    hsame_trans package.right.right.right.right.right.right ledgerEmpty
  have provenanceSelf : hsame provenance provenance :=
    hsame_refl provenance
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance provenanceSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  exact And.intro cert provenanceEmpty

theorem TopGroupRootPublicThreshold_namecert_surface
    {groupSource topologySource product inverse neighbourhood ledger classifier provenance :
      BHist} :
    TopGroupRootPublicThresholdPacket groupSource topologySource product inverse neighbourhood
        ledger classifier provenance ->
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame ∧ hsame provenance BHist.Empty := by
  intro packet
  have provenanceSelf : hsame provenance provenance :=
    hsame_refl provenance
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance provenanceSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  exact And.intro cert packet.right.right.right.right.right

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

theorem TopGroupRootThresholdPackage_source_ledger_empty_spine
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame (append (append group topology) (append ledger provenance)) BHist.Empty ∧
        Cont group topology product ∧ Cont product inverse ledger ∧ hsame provenance ledger := by
  intro package
  have productEmpty : hsame product BHist.Empty :=
    hsame_trans package.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro package.left package.right.left))
  have ledgerEmpty : hsame ledger BHist.Empty :=
    hsame_trans package.right.right.right.right.right.left
      (append_eq_empty_iff.mpr (And.intro productEmpty package.right.right.right.right.left))
  have provenanceEmpty : hsame provenance BHist.Empty :=
    hsame_trans package.right.right.right.right.right.right ledgerEmpty
  have leftEmpty : hsame (append group topology) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro package.left package.right.left)
  have rightEmpty : hsame (append ledger provenance) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro ledgerEmpty provenanceEmpty)
  have spineEmpty : hsame (append (append group topology) (append ledger provenance))
      BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro leftEmpty rightEmpty)
  exact And.intro spineEmpty
    (And.intro package.right.right.right.left
      (And.intro package.right.right.right.right.right.left
        package.right.right.right.right.right.right))

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

theorem TopGroupRootThresholdPackage_continuity_classifier_stability
    {group topology product inverse neighborhood ledger provenance product' inverse' ledger' :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame inverse inverse' ->
          Cont product' inverse' ledger' ->
            hsame ledger ledger' ∧ UnaryHistory product' ∧ UnaryHistory inverse' ∧
              UnaryHistory ledger' := by
  intro package sameProduct sameInverse ledgerCont'
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have ledgerCont : Cont product inverse ledger :=
    package.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProduct sameInverse ledgerCont ledgerCont'
  have productUnary' : UnaryHistory product' :=
    unary_transport boundary.right.right.left sameProduct
  have inverseUnary' : UnaryHistory inverse' :=
    unary_transport boundary.right.right.right.left sameInverse
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed productUnary' inverseUnary' ledgerCont'
  exact And.intro sameLedger
    (And.intro productUnary' (And.intro inverseUnary' ledgerUnary'))

theorem TopGroupRootThresholdPackage_product_neighborhood_transport
    {group topology product inverse neighborhood ledger provenance product' neighborhood'
      productNeighborhood transported : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame product product' ->
        hsame neighborhood neighborhood' ->
          Cont product neighborhood productNeighborhood ->
            Cont product' neighborhood' transported ->
              hsame productNeighborhood transported ∧ UnaryHistory product' ∧
                UnaryHistory neighborhood' ∧ UnaryHistory transported := by
  intro package sameProduct sameNeighborhood productNeighborhoodCont transportedCont
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have sameResult : hsame productNeighborhood transported :=
    cont_respects_hsame sameProduct sameNeighborhood productNeighborhoodCont transportedCont
  have productUnary' : UnaryHistory product' :=
    unary_transport boundary.right.right.left sameProduct
  have neighborhoodUnary' : UnaryHistory neighborhood' :=
    unary_transport boundary.right.right.right.right.left sameNeighborhood
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed productUnary' neighborhoodUnary' transportedCont
  exact And.intro sameResult
    (And.intro productUnary' (And.intro neighborhoodUnary' transportedUnary))

theorem TopGroupRootThresholdPackage_inverse_neighborhood_transport
    {group topology product inverse neighborhood ledger provenance inverseLedger inverseLedger'
      inverse' neighborhood' : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      hsame inverse inverse' ->
        hsame neighborhood neighborhood' ->
          Cont inverse neighborhood inverseLedger ->
            Cont inverse' neighborhood' inverseLedger' ->
              hsame inverseLedger inverseLedger' ∧ UnaryHistory inverse' ∧
                UnaryHistory neighborhood' ∧ UnaryHistory inverseLedger' ∧
                  hsame provenance ledger := by
  intro package sameInverse sameNeighborhood inverseLedgerCont inverseLedgerCont'
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have sameResult : hsame inverseLedger inverseLedger' :=
    cont_respects_hsame sameInverse sameNeighborhood inverseLedgerCont inverseLedgerCont'
  have inverseUnary' : UnaryHistory inverse' :=
    unary_transport boundary.right.right.right.left sameInverse
  have neighborhoodUnary' : UnaryHistory neighborhood' :=
    unary_transport boundary.right.right.right.right.left sameNeighborhood
  have inverseLedgerUnary' : UnaryHistory inverseLedger' :=
    unary_cont_closed inverseUnary' neighborhoodUnary' inverseLedgerCont'
  exact And.intro sameResult
    (And.intro inverseUnary'
      (And.intro neighborhoodUnary'
        (And.intro inverseLedgerUnary' boundary.right.right.right.right.right.right.right)))

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

theorem TopGroupRootThresholdPackage_operation_ledger_obligation
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      consumerLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger consumerLedger ->
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧
              UnaryHistory consumerLedger ∧
                hsame consumerLedger
                  (append (append product neighborhood) (append inverse neighborhood)) ∧
                  hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productRow inverseRow consumerRow
  have boundary :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productRow
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseRow
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed productLedgerUnary inverseLedgerUnary consumerRow
  have consumerReadback :
      hsame consumerLedger (append (append product neighborhood) (append inverse neighborhood)) := by
    cases productRow
    cases inverseRow
    cases consumerRow
    rfl
  exact And.intro productLedgerUnary
    (And.intro inverseLedgerUnary
        (And.intro consumerLedgerUnary
          (And.intro consumerReadback
            (And.intro package.right.right.right.right.right.left
            package.right.right.right.right.right.right))))

theorem TopGroupRootThresholdPackage_downstream_threshold_exactness
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          hsame productLedger (append product neighborhood) ∧
            hsame inverseLedger (append inverse neighborhood) ∧
              hsame ledger (append product inverse) ∧ hsame provenance ledger ∧
                UnaryHistory productLedger ∧ UnaryHistory inverseLedger := by
  intro package productCont inverseCont
  have rows := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed rows.right.right.left rows.right.right.right.right.left productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed rows.right.right.right.left rows.right.right.right.right.left inverseCont
  exact And.intro productCont
    (And.intro inverseCont
        (And.intro package.right.right.right.right.right.left
          (And.intro package.right.right.right.right.right.right
            (And.intro productLedgerUnary inverseLedgerUnary))))

theorem TopGroupRootThresholdPackage_inverse_cont_ledger_soundness
    {group topology product inverse neighborhood ledger provenance inverseLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont inverse neighborhood inverseLedger ->
        UnaryHistory inverseLedger ∧ hsame inverseLedger (append inverse neighborhood) ∧
          UnaryHistory inverse ∧ UnaryHistory neighborhood ∧ hsame ledger (append product inverse) ∧
            hsame provenance ledger := by
  intro package inverseCont
  have rows :=
    TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed rows.right.right.right.left rows.right.right.right.right.left inverseCont
  exact And.intro inverseLedgerUnary
      (And.intro inverseCont
        (And.intro rows.right.right.right.left
          (And.intro rows.right.right.right.right.left
          (And.intro rows.right.right.right.right.right.right.left
            rows.right.right.right.right.right.right.right))))

theorem TopGroupRootSourceFiber_export_continuity
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger
      exportLedger : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont productLedger inverseLedger exportLedger ->
            UnaryHistory productLedger ∧ UnaryHistory inverseLedger ∧ UnaryHistory exportLedger ∧
              hsame exportLedger (append productLedger inverseLedger) ∧
                hsame ledger (append product inverse) ∧ hsame provenance ledger := by
  intro package productCont inverseCont exportCont
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  have productLedgerUnary : UnaryHistory productLedger :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left productCont
  have inverseLedgerUnary : UnaryHistory inverseLedger :=
    unary_cont_closed boundary.right.right.right.left boundary.right.right.right.right.left
      inverseCont
  have exportLedgerUnary : UnaryHistory exportLedger :=
    unary_cont_closed productLedgerUnary inverseLedgerUnary exportCont
  exact And.intro productLedgerUnary
    (And.intro inverseLedgerUnary
      (And.intro exportLedgerUnary
        (And.intro exportCont
          (And.intro package.right.right.right.right.right.left
            package.right.right.right.right.right.right))))

theorem TopGroupRootSourceFiber_export_common_cont_ledger
    {group topology product inverse neighborhood ledger provenance productLedger inverseLedger :
      BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont product neighborhood productLedger ->
        Cont inverse neighborhood inverseLedger ->
          Cont product inverse ledger ∧ hsame provenance ledger ∧ UnaryHistory productLedger ∧
            UnaryHistory inverseLedger ∧ UnaryHistory ledger := by
  intro package productLedgerCont inverseLedgerCont
  have consumers :=
    TopGroupRootThresholdPackage_consumer_exhaustion package productLedgerCont inverseLedgerCont
  have ledgerScope := TopGroupRootThresholdPackage_continuity_ledger_scope package
  exact And.intro ledgerScope.left
    (And.intro consumers.right.right.right.right.right
      (And.intro consumers.right.right.left
        (And.intro consumers.right.right.right.left ledgerScope.right.left)))

theorem TopGroupRootThresholdPackage_public_certificate_boundary
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance) (fun row : BHist => hsame row provenance) hsame ∧
          GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory product ∧
            UnaryHistory inverse ∧ UnaryHistory ledger ∧ hsame ledger (append product inverse) ∧
              hsame provenance ledger := by
  intro package
  have boundary := TopGroupRootThresholdPackage_source_coupled_continuity_boundary package
  exact And.intro (TopGroupRootThresholdPackage_export_boundary_certificate package).left
    (And.intro boundary.left
      (And.intro boundary.right.left
        (And.intro boundary.right.right.left
          (And.intro boundary.right.right.right.left
            (And.intro boundary.right.right.right.right.right.left
              (And.intro boundary.right.right.right.right.right.right.left
                boundary.right.right.right.right.right.right.right))))))
end BEDC.Derived.TopGroupUp
