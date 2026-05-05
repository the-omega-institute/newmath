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

end BEDC.Derived.ManifoldUp
