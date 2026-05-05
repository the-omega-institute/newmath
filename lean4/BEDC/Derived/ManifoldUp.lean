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

end BEDC.Derived.ManifoldUp
