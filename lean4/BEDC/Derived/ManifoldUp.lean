import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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
