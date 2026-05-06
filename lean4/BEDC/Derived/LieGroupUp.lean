import BEDC.Derived.GroupUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LieGroupSingleton_operation_smoothness_obligation {h k product domain value : BHist} :
    GroupSingletonCarrier h ->
      GroupSingletonCarrier k ->
      Cont h k product ->
      Cont BHist.Empty product domain ->
      Cont product BHist.Empty value ->
        hsame product BHist.Empty ∧ ManifoldSingletonCarrier product ∧
          hsame (GroupSingletonInv h) BHist.Empty ∧
            ManifoldSingletonCarrier (GroupSingletonInv h) ∧ hsame domain BHist.Empty ∧
              hsame value BHist.Empty ∧ UnaryHistory value := by
  intro carrierH carrierK productReadback domainReadback valueReadback
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productReadback (cont_left_unit BHist.Empty)
  have productManifold : ManifoldSingletonCarrier product :=
    productEmpty
  have inverseEmpty : hsame (GroupSingletonInv h) BHist.Empty := by
    rfl
  have inverseManifold : ManifoldSingletonCarrier (GroupSingletonInv h) :=
    inverseEmpty
  have chartRows :=
    ManifoldSingleton_chart_coverage productManifold domainReadback valueReadback
  exact And.intro productEmpty
    (And.intro productManifold
      (And.intro inverseEmpty
        (And.intro inverseManifold
          (And.intro chartRows.left
            (And.intro chartRows.right.right.left chartRows.right.right.right)))))

def LieGroupSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LieGroupSingletonMul (h k : BHist) : BHist :=
  append h k

def LieGroupSingletonInv (_h : BHist) : BHist :=
  BHist.Empty

theorem LieGroupSingleton_operation_smoothness {h k mulChart invChart : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k ->
      Cont BHist.Empty (LieGroupSingletonMul h k) mulChart ->
        Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
          hsame mulChart BHist.Empty ∧ hsame invChart BHist.Empty ∧
            UnaryHistory mulChart ∧ UnaryHistory invChart := by
  intro carrierH carrierK mulChartRow invChartRow
  have mulEndpointEmpty : hsame (LieGroupSingletonMul h k) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierH carrierK)
  have mulChartEndpoint : hsame mulChart (LieGroupSingletonMul h k) :=
    cont_left_unit_result mulChartRow
  have mulChartEmpty : hsame mulChart BHist.Empty :=
    hsame_trans mulChartEndpoint mulEndpointEmpty
  have invChartEndpoint : hsame invChart (LieGroupSingletonInv h) :=
    cont_left_unit_result invChartRow
  have invChartEmpty : hsame invChart BHist.Empty :=
    invChartEndpoint
  have mulChartUnary : UnaryHistory mulChart :=
    unary_transport unary_empty (hsame_symm mulChartEmpty)
  have invChartUnary : UnaryHistory invChart :=
    unary_transport unary_empty (hsame_symm invChartEmpty)
  exact And.intro mulChartEmpty
    (And.intro invChartEmpty (And.intro mulChartUnary invChartUnary))

theorem LieGroupSingleton_semantic_name_certificate :
    SemanticNameCert
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h k : BHist =>
          GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h ∧
            GroupSingletonCarrier k ∧ ManifoldSingletonCarrier k ∧ hsame h k) ∧
      (forall {h k product : BHist}, GroupSingletonCarrier h -> GroupSingletonCarrier k ->
        Cont h k product ->
          GroupSingletonCarrier product ∧ ManifoldSingletonCarrier product ∧
            UnaryHistory product) := by
  have emptyCarrier :
      GroupSingletonCarrier BHist.Empty ∧ ManifoldSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier.left
            (And.intro carrier.right
              (And.intro carrier.left (And.intro carrier.right (hsame_refl h))))
        equiv_symm := by
          intro h k classified
          exact And.intro classified.right.right.left
            (And.intro classified.right.right.right.left
              (And.intro classified.left
                (And.intro classified.right.left
                  (hsame_symm classified.right.right.right.right))))
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro classifiedHK.left
            (And.intro classifiedHK.right.left
              (And.intro classifiedKR.right.right.left
                (And.intro classifiedKR.right.right.right.left
                  (hsame_trans classifiedHK.right.right.right.right
                    classifiedKR.right.right.right.right))))
        carrier_respects_equiv := by
          intro h k classified _source
          exact And.intro classified.right.right.left classified.right.right.right.left
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }
  · intro h k product carrierH carrierK productRow
    have productEmpty : hsame product BHist.Empty := by
      exact productRow.trans (append_eq_empty_iff.mpr (And.intro carrierH carrierK))
    exact And.intro productEmpty
      (And.intro productEmpty (unary_transport unary_empty (hsame_symm productEmpty)))

def LieGroupSingletonClassifier (h k : BHist) : Prop :=
  LieGroupSingletonCarrier h ∧ LieGroupSingletonCarrier k ∧ hsame h k

theorem LieGroupSingleton_carrier_obligation :
    SemanticNameCert LieGroupSingletonCarrier LieGroupSingletonCarrier LieGroupSingletonCarrier
        LieGroupSingletonClassifier ∧
      (forall {h : BHist}, LieGroupSingletonCarrier h ->
        GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h ∧ UnaryHistory h) ∧
      (forall {h k : BHist}, LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k ->
        LieGroupSingletonCarrier (GroupSingletonMul h k) ∧
          LieGroupSingletonClassifier (GroupSingletonMul h k) BHist.Empty) ∧
      (forall {h : BHist}, LieGroupSingletonCarrier h ->
        LieGroupSingletonCarrier (GroupSingletonInv h) ∧
          LieGroupSingletonClassifier (GroupSingletonInv h) BHist.Empty) := by
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : LieGroupSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
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
          intro h k classified _carrierH
          exact classified.right.left
      }
      pattern_sound := by
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
  · constructor
    · intro h carrier
      exact And.intro carrier
        (And.intro carrier (unary_transport unary_empty (hsame_symm carrier)))
    · constructor
      · intro h k carrierH carrierK
        have productCarrier : LieGroupSingletonCarrier (GroupSingletonMul h k) := by
          exact append_eq_empty_iff.mpr (And.intro carrierH carrierK)
        exact And.intro productCarrier
          (And.intro productCarrier
            (And.intro emptyCarrier (hsame_trans productCarrier (hsame_symm emptyCarrier))))
      · intro h _carrier
        exact And.intro emptyCarrier emptyClassified

theorem LieGroupSingletonOperation_smoothness {x y product inverse transition : BHist} :
    GroupSingletonCarrier x -> GroupSingletonCarrier y -> ManifoldSingletonCarrier x ->
      ManifoldSingletonCarrier y -> Cont x y product -> Cont product BHist.Empty inverse ->
        Cont product inverse transition ->
          GroupSingletonClassifier product inverse ∧ ManifoldSingletonCarrier product ∧
            ManifoldSingletonCarrier inverse ∧ hsame transition BHist.Empty ∧
              UnaryHistory transition := by
  intro carrierX carrierY _manifoldX _manifoldY productRow inverseRow transitionRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierX carrierY productRow (cont_left_unit BHist.Empty)
  have inverseProduct : hsame inverse product :=
    cont_right_unit_result inverseRow
  have inverseEmpty : hsame inverse BHist.Empty :=
    hsame_trans inverseProduct productEmpty
  have transitionEmpty : hsame transition BHist.Empty :=
    cont_respects_hsame productEmpty inverseEmpty transitionRow (cont_left_unit BHist.Empty)
  have classified : GroupSingletonClassifier product inverse :=
    And.intro productEmpty
      (And.intro inverseEmpty (hsame_trans productEmpty (hsame_symm inverseEmpty)))
  have transitionUnary : UnaryHistory transition :=
    unary_transport unary_empty (hsame_symm transitionEmpty)
  exact And.intro classified
    (And.intro productEmpty (And.intro inverseEmpty (And.intro transitionEmpty transitionUnary)))

end BEDC.Derived.LieGroupUp
