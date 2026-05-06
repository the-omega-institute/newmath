import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ManifoldSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

theorem ManifoldSingletonCarrier_topology_scope {h : BHist} :
    ManifoldSingletonCarrier h -> hsame h BHist.Empty ∧ UnaryHistory h ∧ Cont BHist.Empty h h := by
  intro carrier
  exact And.intro carrier
    (And.intro (unary_transport unary_empty (hsame_symm carrier)) (cont_left_unit h))

theorem ManifoldSingleton_chart_coverage {h domain value : BHist} :
    ManifoldSingletonCarrier h -> Cont BHist.Empty h domain -> Cont h BHist.Empty value ->
      hsame domain BHist.Empty ∧ hsame value h ∧ hsame value BHist.Empty ∧ UnaryHistory value := by
  intro carrier domainReadback valueReadback
  have sameDomainH : hsame domain h :=
    cont_left_unit_result domainReadback
  have domainEmpty : hsame domain BHist.Empty :=
    hsame_trans sameDomainH carrier
  have valueH : hsame value h :=
    cont_right_unit_result valueReadback
  have valueEmpty : hsame value BHist.Empty :=
    hsame_trans valueH carrier
  have valueUnary : UnaryHistory value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  exact And.intro domainEmpty
    (And.intro valueH (And.intro valueEmpty valueUnary))

theorem ManifoldSingleton_semanticNameCert :
    SemanticNameCert ManifoldSingletonCarrier ManifoldSingletonCarrier ManifoldSingletonCarrier
        (fun h k : BHist =>
          ManifoldSingletonCarrier h ∧ ManifoldSingletonCarrier k ∧ hsame h k) ∧
      (forall {h : BHist}, ManifoldSingletonCarrier h -> UnaryHistory h ∧ Cont BHist.Empty h h) := by
  have emptyCarrier : ManifoldSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro classifiedHK.left
            (And.intro classifiedKR.right.left
              (hsame_trans classifiedHK.right.right classifiedKR.right.right))
        carrier_respects_equiv := by
          intro h k classified _sourceH
          exact classified.right.left
      }
      pattern_sound := by
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
  · intro h carrier
    exact (ManifoldSingletonCarrier_topology_scope carrier).right

theorem ManifoldSingleton_chart_value_transport {h k : BHist} :
    ManifoldSingletonCarrier h -> ManifoldSingletonCarrier k ->
      hsame h k ∧ UnaryHistory h ∧ UnaryHistory k ∧ Cont BHist.Empty h h ∧
        Cont BHist.Empty k k := by
  intro carrierH carrierK
  have hRows := ManifoldSingletonCarrier_topology_scope carrierH
  have kRows := ManifoldSingletonCarrier_topology_scope carrierK
  have sameHK : hsame h k := hsame_trans hRows.left (hsame_symm kRows.left)
  exact And.intro sameHK
    (And.intro hRows.right.left
      (And.intro kRows.right.left
        (And.intro hRows.right.right kRows.right.right)))

theorem ManifoldSingleton_chart_coordinate_carrier_transport
    {source target sourceDomain targetDomain sourceCoord targetCoord : BHist} :
    UnaryHistory source -> UnaryHistory target -> hsame source target ->
      Cont BHist.Empty source sourceDomain -> Cont BHist.Empty target targetDomain ->
        Cont BHist.Empty source sourceCoord -> Cont BHist.Empty target targetCoord ->
          hsame sourceDomain targetDomain ∧ hsame sourceCoord targetCoord := by
  intro _sourceCarrier _targetCarrier sameSourceTarget sourceDomainReadback targetDomainReadback
  intro sourceCoordReadback targetCoordReadback
  have sameSourceDomain : hsame sourceDomain source :=
    cont_left_unit_result sourceDomainReadback
  have sameTargetDomain : hsame targetDomain target :=
    cont_left_unit_result targetDomainReadback
  have sameSourceCoord : hsame sourceCoord source :=
    cont_left_unit_result sourceCoordReadback
  have sameTargetCoord : hsame targetCoord target :=
    cont_left_unit_result targetCoordReadback
  exact And.intro
    (hsame_trans sameSourceDomain
      (hsame_trans sameSourceTarget (hsame_symm sameTargetDomain)))
    (hsame_trans sameSourceCoord
      (hsame_trans sameSourceTarget (hsame_symm sameTargetCoord)))

structure ManifoldChartCoordinateTransportRow where
  package : BHist
  chartIndex : BHist
  source : BHist
  target : BHist
  sourceCarrier : ManifoldSingletonCarrier source
  targetCarrier : ManifoldSingletonCarrier target
  sourceValue : BHist
  targetValue : BHist
  sourceReadback : Cont BHist.Empty source sourceValue
  targetReadback : Cont BHist.Empty target targetValue
  coordinateClassified : hsame sourceValue targetValue
  sourceUnary : UnaryHistory sourceValue
  targetUnary : UnaryHistory targetValue

theorem ManifoldSingleton_atlas_index_exhaustion {chart overlap domain : BHist} :
    ManifoldSingletonCarrier chart -> Cont BHist.Empty chart domain -> Cont chart chart overlap ->
      hsame chart BHist.Empty ∧ hsame domain BHist.Empty ∧ hsame overlap BHist.Empty ∧
        UnaryHistory domain ∧ UnaryHistory overlap := by
  intro carrier domainReadback overlapReadback
  have chartEmpty : hsame chart BHist.Empty := carrier
  have sameDomainChart : hsame domain chart :=
    cont_left_unit_result domainReadback
  have domainEmpty : hsame domain BHist.Empty :=
    hsame_trans sameDomainChart chartEmpty
  have overlapEmpty : hsame overlap BHist.Empty := by
    have sameOverlapAppend :
        hsame overlap (append BHist.Empty BHist.Empty) :=
      cont_respects_hsame chartEmpty chartEmpty overlapReadback
        (cont_left_unit BHist.Empty)
    exact hsame_trans sameOverlapAppend (append_empty_left BHist.Empty)
  have domainUnary : UnaryHistory domain :=
    unary_transport unary_empty (hsame_symm domainEmpty)
  have overlapUnary : UnaryHistory overlap :=
    unary_transport unary_empty (hsame_symm overlapEmpty)
  exact And.intro chartEmpty
    (And.intro domainEmpty (And.intro overlapEmpty (And.intro domainUnary overlapUnary)))

def ManifoldAtlasPackage (base index domain chart transition : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory index ∧ UnaryHistory domain ∧ UnaryHistory chart ∧
    UnaryHistory transition ∧ Cont base index domain ∧ Cont domain chart transition

def ManifoldAtlasClassifier
    (base index domain chart transition base' index' domain' chart' transition' : BHist) :
    Prop :=
  hsame base base' ∧ hsame index index' ∧ hsame domain domain' ∧ hsame chart chart' ∧
    hsame transition transition'

theorem ManifoldAtlasPackage_semantic_name_certificate :
    SemanticNameCert
      (fun transition : BHist =>
        ∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart transition)
      (fun transition : BHist =>
        ∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart transition)
      (fun transition : BHist =>
        ∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart transition)
      (fun left right : BHist =>
        (∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart left) ∧
          (∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart right) ∧
            hsame left right) := by
  let AtlasTransition := fun transition : BHist =>
    ∃ base index domain chart : BHist, ManifoldAtlasPackage base index domain chart transition
  have emptyAtlas : AtlasTransition BHist.Empty := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (And.intro unary_empty
              (And.intro unary_empty
                (And.intro unary_empty
                  (And.intro unary_empty
                    (And.intro unary_empty
                      (And.intro (cont_left_unit BHist.Empty)
                        (cont_left_unit BHist.Empty))))))))))
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyAtlas
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro left right classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro left mid right classifiedLM classifiedMR
        exact And.intro classifiedLM.left
          (And.intro classifiedMR.right.left
            (hsame_trans classifiedLM.right.right classifiedMR.right.right))
      carrier_respects_equiv := by
        intro left right classified _carrierLeft
        exact classified.right.left
    }
    pattern_sound := by
      intro transition carrier
      exact carrier
    ledger_sound := by
      intro transition carrier
      exact carrier
  }

theorem ManifoldAtlasPackage_classifier_transport
    {base index domain chart transition base' index' domain' chart' transition' : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      ManifoldAtlasClassifier base index domain chart transition base' index' domain' chart'
        transition' ->
        ManifoldAtlasPackage base' index' domain' chart' transition' ∧ UnaryHistory base' ∧
          UnaryHistory index' ∧ Cont base' index' domain' ∧
            Cont domain' chart' transition' := by
  intro package classified
  have baseUnary : UnaryHistory base := package.left
  have indexUnary : UnaryHistory index := package.right.left
  have domainRow : Cont base index domain := package.right.right.right.right.right.left
  have transitionRow : Cont domain chart transition :=
    package.right.right.right.right.right.right
  cases classified.left
  cases classified.right.left
  cases classified.right.right.left
  cases classified.right.right.right.left
  cases classified.right.right.right.right
  exact And.intro package
    (And.intro baseUnary (And.intro indexUnary (And.intro domainRow transitionRow)))

theorem ManifoldAtlasPackage_transition_composition_target
    {base index domain chart transition next composite direct : BHist} :
    ManifoldAtlasPackage base index domain chart transition -> UnaryHistory next ->
      Cont transition next composite -> Cont domain (append chart next) direct ->
        hsame composite direct ∧ UnaryHistory composite ∧ UnaryHistory direct := by
  intro package nextUnary transitionNext domainChartNext
  have domainUnary : UnaryHistory domain := package.right.right.left
  have chartUnary : UnaryHistory chart := package.right.right.right.left
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  have domainChart : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have compositeUnary : UnaryHistory composite :=
    unary_cont_closed transitionUnary nextUnary transitionNext
  have chartNextUnary : UnaryHistory (append chart next) :=
    unary_cont_closed chartUnary nextUnary (cont_intro rfl)
  have directUnary : UnaryHistory direct :=
    unary_cont_closed domainUnary chartNextUnary domainChartNext
  cases domainChart
  cases transitionNext
  cases domainChartNext
  exact And.intro (append_assoc domain chart next) (And.intro compositeUnary directUnary)

theorem ManifoldAtlasPackage_pairwise_overlap_readback
    {base index domain chart transition pair : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      Cont base index pair ->
        hsame pair domain ∧ Cont pair chart transition ∧ hsame transition (append pair chart) ∧
          UnaryHistory pair ∧ UnaryHistory transition := by
  intro package pairRow
  have baseUnary : UnaryHistory base := package.left
  have indexUnary : UnaryHistory index := package.right.left
  have domainRow : Cont base index domain := package.right.right.right.right.right.left
  have transitionRow : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have samePairDomain : hsame pair domain := cont_deterministic pairRow domainRow
  have pairUnary : UnaryHistory pair := unary_cont_closed baseUnary indexUnary pairRow
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  cases samePairDomain
  exact And.intro (hsame_refl domain)
    (And.intro transitionRow
      (And.intro transitionRow (And.intro pairUnary transitionUnary)))

theorem ManifoldAtlasPackage_chart_domain_intersection_open
    {base indexI indexJ domainI domainJ chart transitionI transitionJ overlap : BHist} :
    ManifoldAtlasPackage base indexI domainI chart transitionI ->
      ManifoldAtlasPackage base indexJ domainJ chart transitionJ ->
        Cont domainI domainJ overlap ->
          UnaryHistory overlap ∧ hsame overlap (append (append base indexI) (append base indexJ)) := by
  intro packageI packageJ overlapRow
  have domainIUnary : UnaryHistory domainI := packageI.right.right.left
  have domainJUnary : UnaryHistory domainJ := packageJ.right.right.left
  have domainIRow : Cont base indexI domainI := packageI.right.right.right.right.right.left
  have domainJRow : Cont base indexJ domainJ := packageJ.right.right.right.right.right.left
  have overlapUnary : UnaryHistory overlap :=
    unary_cont_closed domainIUnary domainJUnary overlapRow
  cases domainIRow
  cases domainJRow
  cases overlapRow
  exact And.intro overlapUnary (hsame_refl (append (append base indexI) (append base indexJ)))

theorem ManifoldAtlasPackage_transition_composition_scope
    {base index domain chart transition next composed direct : BHist} :
    ManifoldAtlasPackage base index domain chart transition -> UnaryHistory next ->
      Cont transition next composed -> Cont domain (append chart next) direct ->
        hsame composed direct ∧ UnaryHistory composed ∧ UnaryHistory direct := by
  intro package nextUnary transitionNext domainChartNext
  have domainUnary : UnaryHistory domain := package.right.right.left
  have chartUnary : UnaryHistory chart := package.right.right.right.left
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  have domainChart : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have chartNextUnary : UnaryHistory (append chart next) :=
    unary_cont_closed chartUnary nextUnary (cont_intro rfl)
  have composedDirect : hsame composed direct :=
    cont_assoc_hsame domainChart transitionNext (cont_intro rfl) domainChartNext
  have composedUnary : UnaryHistory composed :=
    unary_cont_closed transitionUnary nextUnary transitionNext
  have directUnary : UnaryHistory direct :=
    unary_cont_closed domainUnary chartNextUnary domainChartNext
  exact And.intro composedDirect (And.intro composedUnary directUnary)

theorem ManifoldAtlasPackage_transition_source_readback
    {base index domain chart transition : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      UnaryHistory transition ∧ hsame transition (append (append base index) chart) ∧
        Cont (append base index) chart transition ∧ Cont base index domain ∧
          Cont domain chart transition := by
  intro package
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  have domainRow : Cont base index domain := package.right.right.right.right.right.left
  have transitionRow : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have sourceReadback : hsame transition (append (append base index) chart) := by
    cases domainRow
    cases transitionRow
    rfl
  have carriedTransition : Cont (append base index) chart transition := by
    cases domainRow
    exact transitionRow
  exact And.intro transitionUnary
    (And.intro sourceReadback
      (And.intro carriedTransition (And.intro domainRow transitionRow)))

theorem ManifoldAtlasPackage_transition_closure {base index domain chart transition : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      UnaryHistory transition ∧ hsame transition (append domain chart) := by
  intro package
  exact And.intro package.right.right.right.right.left
    package.right.right.right.right.right.right

theorem ManifoldAtlasPackage_transition_append_readback {base index domain chart transition : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      hsame transition (append base (append index chart)) ∧
        Cont (append base index) chart transition ∧ UnaryHistory transition := by
  intro package
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  have domainRow : Cont base index domain := package.right.right.right.right.right.left
  have transitionRow : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have appendTransition : hsame transition (append base (append index chart)) := by
    cases domainRow
    cases transitionRow
    exact append_assoc base index chart
  have composedRow : Cont (append base index) chart transition := by
    cases domainRow
    exact transitionRow
  exact And.intro appendTransition (And.intro composedRow transitionUnary)

theorem ManifoldAtlasPackage_transition_composition_readback
    {base index domain chart transition : BHist} :
    ManifoldAtlasPackage base index domain chart transition ->
      hsame transition (append base (append index chart)) ∧
        hsame transition (append (append base index) chart) ∧ UnaryHistory transition := by
  intro package
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.left
  have domainRow : Cont base index domain := package.right.right.right.right.right.left
  have transitionRow : Cont domain chart transition :=
    package.right.right.right.right.right.right
  have sameTransitionLeft : hsame transition (append (append base index) chart) := by
    cases domainRow
    exact transitionRow
  have sameTransitionNested : hsame transition (append base (append index chart)) :=
    hsame_trans sameTransitionLeft (append_assoc base index chart)
  exact And.intro sameTransitionNested (And.intro sameTransitionLeft transitionUnary)

structure ManifoldAtlasObligationInventory where
  base : BHist
  index : BHist
  domain : BHist
  chart : BHist
  transition : BHist
  package : ManifoldAtlasPackage base index domain chart transition
  semanticCertificate :
    SemanticNameCert ManifoldSingletonCarrier ManifoldSingletonCarrier ManifoldSingletonCarrier
      (fun h k : BHist =>
        ManifoldSingletonCarrier h ∧ ManifoldSingletonCarrier k ∧ hsame h k)
  classifierTransport :
    forall {base' index' domain' chart' transition' : BHist},
      ManifoldAtlasClassifier base index domain chart transition base' index' domain' chart'
        transition' ->
        ManifoldAtlasPackage base' index' domain' chart' transition'
  transitionReadback : hsame transition (append base (append index chart))

def ManifoldScopedBoundaryPackage (carrier i j k pair triple : BHist) : Prop :=
  UnaryHistory carrier ∧ UnaryHistory i ∧ UnaryHistory j ∧ UnaryHistory k ∧
    Cont i j pair ∧ Cont pair k triple

theorem ManifoldScopedBoundaryPackage_triple_overlap_source_determinacy
    {carrier i j k pair triple : BHist} :
    ManifoldScopedBoundaryPackage carrier i j k pair triple ->
      UnaryHistory pair ∧ UnaryHistory triple ∧ hsame triple (append i (append j k)) := by
  intro package
  have iUnary : UnaryHistory i := package.right.left
  have jUnary : UnaryHistory j := package.right.right.left
  have kUnary : UnaryHistory k := package.right.right.right.left
  have pairRow : Cont i j pair := package.right.right.right.right.left
  have tripleRow : Cont pair k triple := package.right.right.right.right.right
  have pairUnary : UnaryHistory pair := unary_cont_closed iUnary jUnary pairRow
  have tripleUnary : UnaryHistory triple := unary_cont_closed pairUnary kUnary tripleRow
  cases pairRow
  cases tripleRow
  exact And.intro pairUnary (And.intro tripleUnary (append_assoc i j k))

theorem ManifoldScopedBoundaryPackage_transition_coherence_rows
    {carrier i j k pair triple idRow inverseRow cocycleRow : BHist} :
    ManifoldScopedBoundaryPackage carrier i j k pair triple -> Cont BHist.Empty pair idRow ->
      Cont pair pair inverseRow -> Cont pair triple cocycleRow ->
        UnaryHistory pair ∧ UnaryHistory triple ∧ hsame idRow pair ∧
          hsame inverseRow (append pair pair) ∧ hsame cocycleRow (append pair triple) ∧
            UnaryHistory idRow ∧ UnaryHistory inverseRow ∧ UnaryHistory cocycleRow := by
  intro package idCont inverseCont cocycleCont
  have overlapRows := ManifoldScopedBoundaryPackage_triple_overlap_source_determinacy package
  have pairUnary : UnaryHistory pair := overlapRows.left
  have tripleUnary : UnaryHistory triple := overlapRows.right.left
  have idSame : hsame idRow pair :=
    cont_left_unit_result idCont
  have inverseSame : hsame inverseRow (append pair pair) :=
    inverseCont
  have cocycleSame : hsame cocycleRow (append pair triple) :=
    cocycleCont
  have idUnary : UnaryHistory idRow :=
    unary_transport pairUnary (hsame_symm idSame)
  have inverseUnary : UnaryHistory inverseRow :=
    unary_cont_closed pairUnary pairUnary inverseCont
  have cocycleUnary : UnaryHistory cocycleRow :=
    unary_cont_closed pairUnary tripleUnary cocycleCont
  exact And.intro pairUnary
    (And.intro tripleUnary
      (And.intro idSame
        (And.intro inverseSame
          (And.intro cocycleSame
            (And.intro idUnary (And.intro inverseUnary cocycleUnary))))))

theorem ManifoldScopedBoundaryPackage_reassociated_source {carrier i j k pair triple : BHist} :
    ManifoldScopedBoundaryPackage carrier i j k pair triple ->
      ∃ right : BHist, Cont j k right ∧ Cont i right triple ∧
        hsame triple (append i (append j k)) := by
  intro package
  have pairRow : Cont i j pair := package.right.right.right.right.left
  have tripleRow : Cont pair k triple := package.right.right.right.right.right
  refine Exists.intro (append j k) ?_
  have rightRow : Cont j k (append j k) := cont_intro rfl
  have reassociatedRow : Cont i (append j k) triple := by
    cases pairRow
    cases tripleRow
    exact cont_intro (append_assoc i j k)
  have visibleReadback : hsame triple (append i (append j k)) := by
    cases pairRow
    cases tripleRow
    exact append_assoc i j k
  exact And.intro rightRow (And.intro reassociatedRow visibleReadback)

theorem ManifoldScopedBoundaryPackage_pair_transition_closure
    {carrier i j k pair triple : BHist} :
    ManifoldScopedBoundaryPackage carrier i j k pair triple ->
      UnaryHistory pair ∧ hsame pair (append i j) ∧ UnaryHistory triple ∧
        hsame triple (append pair k) := by
  intro package
  have iUnary : UnaryHistory i := package.right.left
  have jUnary : UnaryHistory j := package.right.right.left
  have kUnary : UnaryHistory k := package.right.right.right.left
  have pairRow : Cont i j pair := package.right.right.right.right.left
  have tripleRow : Cont pair k triple := package.right.right.right.right.right
  have pairUnary : UnaryHistory pair := unary_cont_closed iUnary jUnary pairRow
  have tripleUnary : UnaryHistory triple := unary_cont_closed pairUnary kUnary tripleRow
  exact And.intro pairUnary (And.intro pairRow (And.intro tripleUnary tripleRow))

theorem ManifoldSingleton_scoped_boundary_instance {chart domain value transition : BHist} :
    ManifoldSingletonCarrier chart -> Cont BHist.Empty chart domain ->
      Cont chart BHist.Empty value -> Cont domain value transition ->
        hsame chart BHist.Empty ∧ hsame domain BHist.Empty ∧ hsame value BHist.Empty ∧
          hsame transition BHist.Empty ∧ UnaryHistory chart ∧ UnaryHistory domain ∧
            UnaryHistory value ∧ UnaryHistory transition := by
  intro carrier domainReadback valueReadback transitionReadback
  have chartEmpty : hsame chart BHist.Empty := carrier
  have sameDomainChart : hsame domain chart :=
    cont_left_unit_result domainReadback
  have domainEmpty : hsame domain BHist.Empty :=
    hsame_trans sameDomainChart chartEmpty
  have sameValueChart : hsame value chart :=
    cont_right_unit_result valueReadback
  have valueEmpty : hsame value BHist.Empty :=
    hsame_trans sameValueChart chartEmpty
  have transitionEmpty : hsame transition BHist.Empty :=
    cont_respects_hsame domainEmpty valueEmpty transitionReadback (cont_left_unit BHist.Empty)
  have chartUnary : UnaryHistory chart :=
    unary_transport unary_empty (hsame_symm chartEmpty)
  have domainUnary : UnaryHistory domain :=
    unary_transport unary_empty (hsame_symm domainEmpty)
  have valueUnary : UnaryHistory value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  have transitionUnary : UnaryHistory transition :=
    unary_transport unary_empty (hsame_symm transitionEmpty)
  exact And.intro chartEmpty
    (And.intro domainEmpty
      (And.intro valueEmpty
        (And.intro transitionEmpty
          (And.intro chartUnary
            (And.intro domainUnary (And.intro valueUnary transitionUnary))))))

theorem ManifoldSingleton_domain_exactness {h domain top bottom value : BHist} :
    ManifoldSingletonCarrier h -> Cont BHist.Empty h domain -> Cont h BHist.Empty value ->
      hsame top BHist.Empty -> hsame bottom (BHist.e0 BHist.Empty) ->
        hsame domain top ∧ (hsame domain bottom -> False) ∧ hsame value BHist.Empty ∧
          UnaryHistory h ∧ UnaryHistory domain ∧ UnaryHistory value := by
  intro carrier domainReadback valueReadback topEmpty bottomZero
  have hEmpty : hsame h BHist.Empty := carrier
  have sameDomainH : hsame domain h :=
    cont_left_unit_result domainReadback
  have domainEmpty : hsame domain BHist.Empty :=
    hsame_trans sameDomainH hEmpty
  have domainTop : hsame domain top :=
    hsame_trans domainEmpty (hsame_symm topEmpty)
  have valueH : hsame value h :=
    cont_right_unit_result valueReadback
  have valueEmpty : hsame value BHist.Empty :=
    hsame_trans valueH hEmpty
  have hUnary : UnaryHistory h :=
    unary_transport unary_empty (hsame_symm hEmpty)
  have domainUnary : UnaryHistory domain :=
    unary_transport unary_empty (hsame_symm domainEmpty)
  have valueUnary : UnaryHistory value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  have bottomAbsurd : hsame domain bottom -> False := by
    intro domainBottom
    exact unary_history_hsame_zero_absurd domainUnary (hsame_trans domainBottom bottomZero)
  exact And.intro domainTop
    (And.intro bottomAbsurd
      (And.intro valueEmpty (And.intro hUnary (And.intro domainUnary valueUnary))))

theorem ManifoldSingleton_transition_smoothness {source target result : BHist} :
    ManifoldSingletonCarrier source -> ManifoldSingletonCarrier target -> Cont source target result ->
      hsame result BHist.Empty ∧ hsame result source ∧ hsame result target ∧
        UnaryHistory result := by
  intro sourceCarrier targetCarrier transition
  have emptyTransition : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have resultEmpty : hsame result BHist.Empty :=
    cont_respects_hsame sourceCarrier targetCarrier transition emptyTransition
  have resultSource : hsame result source :=
    hsame_trans resultEmpty (hsame_symm sourceCarrier)
  have resultTarget : hsame result target :=
    hsame_trans resultEmpty (hsame_symm targetCarrier)
  have resultUnary : UnaryHistory result :=
    unary_transport unary_empty (hsame_symm resultEmpty)
  exact And.intro resultEmpty (And.intro resultSource (And.intro resultTarget resultUnary))

structure ManifoldTransitionCoherenceLedger where
  chart : BHist
  domain : BHist
  value : BHist
  selfTransition : BHist
  inverseRound : BHist
  cocycle : BHist
  chartCarrier : ManifoldSingletonCarrier chart
  domainReadback : Cont BHist.Empty chart domain
  valueReadback : Cont chart BHist.Empty value
  identityRow : Cont value value selfTransition
  inverseRoundRow : Cont selfTransition selfTransition inverseRound
  cocycleRow : Cont inverseRound value cocycle

theorem ManifoldSingleton_transition_inverse_boundary {source target forward backward left right : BHist} :
    ManifoldSingletonCarrier source -> ManifoldSingletonCarrier target -> Cont source target forward ->
      Cont target source backward -> Cont forward backward left -> Cont backward forward right ->
        hsame forward BHist.Empty ∧ hsame backward BHist.Empty ∧ hsame left BHist.Empty ∧
          hsame right BHist.Empty ∧ UnaryHistory forward ∧ UnaryHistory backward ∧
            UnaryHistory left ∧ UnaryHistory right := by
  intro sourceCarrier targetCarrier forwardCont backwardCont leftCont rightCont
  have forwardRows :=
    ManifoldSingleton_transition_smoothness sourceCarrier targetCarrier forwardCont
  have backwardRows :=
    ManifoldSingleton_transition_smoothness targetCarrier sourceCarrier backwardCont
  have forwardEmpty : hsame forward BHist.Empty := forwardRows.left
  have backwardEmpty : hsame backward BHist.Empty := backwardRows.left
  have emptyCont : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame forwardEmpty backwardEmpty leftCont emptyCont
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame backwardEmpty forwardEmpty rightCont emptyCont
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro forwardEmpty
    (And.intro backwardEmpty
      (And.intro leftEmpty
        (And.intro rightEmpty
          (And.intro forwardRows.right.right.right
            (And.intro backwardRows.right.right.right (And.intro leftUnary rightUnary))))))

theorem ManifoldSingleton_transition_classifier_stability
    {x y xa xb ya yb source target : BHist} :
    ManifoldSingletonCarrier x -> ManifoldSingletonCarrier y -> hsame x y ->
      Cont BHist.Empty x xa -> Cont BHist.Empty y ya -> Cont BHist.Empty x xb ->
        Cont BHist.Empty y yb -> Cont xa xb source -> Cont ya yb target ->
          hsame xa ya ∧ hsame xb yb ∧ hsame source target ∧ UnaryHistory source ∧
            UnaryHistory target := by
  intro carrierX carrierY sameXY xToXa yToYa xToXb yToYb sourceRow targetRow
  have xUnary : UnaryHistory x :=
    unary_transport unary_empty (hsame_symm carrierX)
  have yUnary : UnaryHistory y :=
    unary_transport unary_empty (hsame_symm carrierY)
  have coordinateSame :=
    ManifoldSingleton_chart_coordinate_carrier_transport xUnary yUnary sameXY xToXa yToYa
      xToXb yToYb
  have xaUnary : UnaryHistory xa :=
    unary_transport xUnary (hsame_symm (cont_left_unit_result xToXa))
  have xbUnary : UnaryHistory xb :=
    unary_transport xUnary (hsame_symm (cont_left_unit_result xToXb))
  have yaUnary : UnaryHistory ya :=
    unary_transport yUnary (hsame_symm (cont_left_unit_result yToYa))
  have ybUnary : UnaryHistory yb :=
    unary_transport yUnary (hsame_symm (cont_left_unit_result yToYb))
  have sourceTarget : hsame source target :=
    cont_respects_hsame coordinateSame.left coordinateSame.right sourceRow targetRow
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed xaUnary xbUnary sourceRow
  have targetUnary : UnaryHistory target :=
    unary_cont_closed yaUnary ybUnary targetRow
  exact And.intro coordinateSame.left
    (And.intro coordinateSame.right
      (And.intro sourceTarget (And.intro sourceUnary targetUnary)))

theorem ManifoldChartCoordinateTransportRow_coordinate_determinacy
    (left right : ManifoldChartCoordinateTransportRow) (sameSource : hsame left.source right.source)
    (sameTarget : hsame left.target right.target) :
    hsame left.sourceValue right.sourceValue ∧ hsame left.targetValue right.targetValue ∧
      UnaryHistory left.sourceValue ∧ UnaryHistory right.sourceValue ∧
        UnaryHistory left.targetValue ∧ UnaryHistory right.targetValue := by
  have sourceSame : hsame left.sourceValue right.sourceValue :=
    cont_respects_hsame (hsame_refl BHist.Empty) sameSource left.sourceReadback right.sourceReadback
  have targetSame : hsame left.targetValue right.targetValue :=
    cont_respects_hsame (hsame_refl BHist.Empty) sameTarget left.targetReadback right.targetReadback
  exact And.intro sourceSame
    (And.intro targetSame
      (And.intro left.sourceUnary
        (And.intro right.sourceUnary (And.intro left.targetUnary right.targetUnary))))

theorem ManifoldSingleton_overlap_inverse_transition {i j ij ji left right : BHist} :
    ManifoldSingletonCarrier i -> ManifoldSingletonCarrier j -> Cont i j ij -> Cont j i ji ->
      Cont ij ji left -> Cont ji ij right ->
        hsame ij BHist.Empty ∧ hsame ji BHist.Empty ∧ hsame left BHist.Empty ∧
          hsame right BHist.Empty ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierI carrierJ transitionIJ transitionJI compositeLeft compositeRight
  have emptyTransition : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have ijEmpty : hsame ij BHist.Empty :=
    cont_respects_hsame carrierI carrierJ transitionIJ emptyTransition
  have jiEmpty : hsame ji BHist.Empty :=
    cont_respects_hsame carrierJ carrierI transitionJI emptyTransition
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame ijEmpty jiEmpty compositeLeft emptyTransition
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame jiEmpty ijEmpty compositeRight emptyTransition
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro ijEmpty
    (And.intro jiEmpty
      (And.intro leftEmpty (And.intro rightEmpty (And.intro leftUnary rightUnary))))

theorem ManifoldSingleton_chart_coordinate_classifier_determinacy
    {source target source0 source1 target0 target1 : BHist} :
    ManifoldSingletonCarrier source -> ManifoldSingletonCarrier target ->
      Cont BHist.Empty source source0 -> Cont BHist.Empty source source1 ->
        Cont BHist.Empty target target0 -> Cont BHist.Empty target target1 ->
          hsame source0 source1 ∧ hsame target0 target1 ∧ hsame source0 target0 ∧
            hsame source1 target1 := by
  intro sourceCarrier targetCarrier sourceReadback0 sourceReadback1 targetReadback0
    targetReadback1
  have sameSource0Source : hsame source0 source :=
    cont_left_unit_result sourceReadback0
  have sameSource1Source : hsame source1 source :=
    cont_left_unit_result sourceReadback1
  have sameTarget0Target : hsame target0 target :=
    cont_left_unit_result targetReadback0
  have sameTarget1Target : hsame target1 target :=
    cont_left_unit_result targetReadback1
  have source0Empty : hsame source0 BHist.Empty :=
    hsame_trans sameSource0Source sourceCarrier
  have source1Empty : hsame source1 BHist.Empty :=
    hsame_trans sameSource1Source sourceCarrier
  have target0Empty : hsame target0 BHist.Empty :=
    hsame_trans sameTarget0Target targetCarrier
  have target1Empty : hsame target1 BHist.Empty :=
    hsame_trans sameTarget1Target targetCarrier
  exact And.intro (hsame_trans source0Empty (hsame_symm source1Empty))
    (And.intro (hsame_trans target0Empty (hsame_symm target1Empty))
      (And.intro (hsame_trans source0Empty (hsame_symm target0Empty))
        (hsame_trans source1Empty (hsame_symm target1Empty))))

theorem ManifoldSingleton_coherence_rows_empty {i j k self pair triple inverse cocycle : BHist} :
    ManifoldSingletonCarrier i -> ManifoldSingletonCarrier j -> ManifoldSingletonCarrier k ->
      Cont i i self -> Cont i j pair -> Cont pair k triple -> Cont self pair inverse ->
        Cont triple self cocycle ->
          hsame self BHist.Empty ∧ hsame pair BHist.Empty ∧ hsame triple BHist.Empty ∧
            hsame inverse BHist.Empty ∧ hsame cocycle BHist.Empty ∧ UnaryHistory self ∧
              UnaryHistory pair ∧ UnaryHistory triple ∧ UnaryHistory inverse ∧
                UnaryHistory cocycle := by
  intro carrierI carrierJ carrierK selfRow pairRow tripleRow inverseRow cocycleRow
  have selfEmpty : hsame self BHist.Empty :=
    cont_respects_hsame carrierI carrierI selfRow (cont_left_unit BHist.Empty)
  have pairEmpty : hsame pair BHist.Empty :=
    cont_respects_hsame carrierI carrierJ pairRow (cont_left_unit BHist.Empty)
  have tripleEmpty : hsame triple BHist.Empty :=
    cont_respects_hsame pairEmpty carrierK tripleRow (cont_left_unit BHist.Empty)
  have inverseEmpty : hsame inverse BHist.Empty :=
    cont_respects_hsame selfEmpty pairEmpty inverseRow (cont_left_unit BHist.Empty)
  have cocycleEmpty : hsame cocycle BHist.Empty :=
    cont_respects_hsame tripleEmpty selfEmpty cocycleRow (cont_left_unit BHist.Empty)
  have selfUnary : UnaryHistory self :=
    unary_transport unary_empty (hsame_symm selfEmpty)
  have pairUnary : UnaryHistory pair :=
    unary_transport unary_empty (hsame_symm pairEmpty)
  have tripleUnary : UnaryHistory triple :=
    unary_transport unary_empty (hsame_symm tripleEmpty)
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm inverseEmpty)
  have cocycleUnary : UnaryHistory cocycle :=
    unary_transport unary_empty (hsame_symm cocycleEmpty)
  exact And.intro selfEmpty
    (And.intro pairEmpty
      (And.intro tripleEmpty
        (And.intro inverseEmpty
          (And.intro cocycleEmpty
            (And.intro selfUnary
              (And.intro pairUnary
                (And.intro tripleUnary (And.intro inverseUnary cocycleUnary))))))))

structure ManifoldChartedCarrier where
  base : BHist
  index : BHist
  domain : BHist
  chart : BHist
  transition : BHist
  base_unary : UnaryHistory base
  index_unary : UnaryHistory index
  domain_unary : UnaryHistory domain
  chart_unary : UnaryHistory chart
  transition_unary : UnaryHistory transition
  domain_row : Cont base index domain
  transition_row : Cont domain chart transition

theorem ManifoldChartedCarrier_atlas_package (M : ManifoldChartedCarrier) :
    ManifoldAtlasPackage M.base M.index M.domain M.chart M.transition ∧
      Cont M.base M.index M.domain ∧ Cont M.domain M.chart M.transition := by
  have package : ManifoldAtlasPackage M.base M.index M.domain M.chart M.transition :=
    And.intro M.base_unary
      (And.intro M.index_unary
        (And.intro M.domain_unary
          (And.intro M.chart_unary
            (And.intro M.transition_unary (And.intro M.domain_row M.transition_row)))))
  exact And.intro package (And.intro M.domain_row M.transition_row)

end BEDC.Derived.ManifoldUp
