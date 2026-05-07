import BEDC.Derived.GroupUp
import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.LieAlgebraUp
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

def LieGroupSingletonConjugationAction (s x : BHist) : BHist :=
  append (append s x) (LieGroupSingletonInv s)

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

theorem LieGroupSingleton_classifier_transport {h h' k k' : BHist} :
    LieGroupSingletonClassifier h h' -> LieGroupSingletonClassifier k k' ->
      LieGroupSingletonClassifier (append h k) (append h' k') ∧
        LieGroupSingletonClassifier BHist.Empty BHist.Empty := by
  intro classifiedH classifiedK
  have productLeft : LieGroupSingletonCarrier (append h k) :=
    append_eq_empty_iff.mpr (And.intro classifiedH.left classifiedK.left)
  have productRight : LieGroupSingletonCarrier (append h' k') :=
    append_eq_empty_iff.mpr (And.intro classifiedH.right.left classifiedK.right.left)
  have productSame : hsame (append h k) (append h' k') :=
    hsame_trans productLeft (hsame_symm productRight)
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  exact And.intro
    (And.intro productLeft (And.intro productRight productSame))
    (And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty)))

theorem LieGroupSingleton_multiplication_smooth_homomorphism {h k product domain value : BHist} :
    LieGroupSingletonCarrier h ->
      LieGroupSingletonCarrier k ->
        Cont h k product ->
          Cont BHist.Empty product domain ->
            Cont product BHist.Empty value ->
              LieGroupSingletonCarrier product ∧
                LieGroupSingletonClassifier product BHist.Empty ∧
                  hsame domain BHist.Empty ∧ hsame value BHist.Empty ∧ UnaryHistory value := by
  intro carrierH carrierK productRow domainRow valueRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productRow (cont_left_unit BHist.Empty)
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have productClassified : LieGroupSingletonClassifier product BHist.Empty :=
    And.intro productEmpty (And.intro emptyCarrier productEmpty)
  have domainEmpty : hsame domain BHist.Empty := by
    have sameDomain : hsame domain product :=
      cont_left_unit_result domainRow
    exact hsame_trans sameDomain productEmpty
  have valueEmpty : hsame value BHist.Empty :=
    cont_respects_hsame productEmpty (hsame_refl BHist.Empty) valueRow
      (cont_left_unit BHist.Empty)
  have valueUnary : UnaryHistory value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  exact And.intro productEmpty
    (And.intro productClassified
      (And.intro domainEmpty (And.intro valueEmpty valueUnary)))

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

theorem LieGroupSingleton_chart_operation_readback {h k product mulChart invChart : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k -> Cont h k product ->
      Cont BHist.Empty product mulChart -> Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
        LieGroupSingletonClassifier product BHist.Empty ∧ ManifoldSingletonCarrier product ∧
          hsame mulChart BHist.Empty ∧ hsame invChart BHist.Empty ∧
            UnaryHistory mulChart ∧ UnaryHistory invChart := by
  intro carrierH carrierK productRow mulChartRow invChartRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productRow (cont_left_unit BHist.Empty)
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have classified : LieGroupSingletonClassifier product BHist.Empty :=
    And.intro productEmpty (And.intro emptyCarrier productEmpty)
  have productManifold : ManifoldSingletonCarrier product :=
    productEmpty
  have mulProduct : hsame mulChart product :=
    cont_left_unit_result mulChartRow
  have mulEmpty : hsame mulChart BHist.Empty :=
    hsame_trans mulProduct productEmpty
  have invEndpoint : hsame invChart (LieGroupSingletonInv h) :=
    cont_left_unit_result invChartRow
  have invEmpty : hsame invChart BHist.Empty :=
    invEndpoint
  have mulUnary : UnaryHistory mulChart :=
    unary_transport unary_empty (hsame_symm mulEmpty)
  have invUnary : UnaryHistory invChart :=
    unary_transport unary_empty (hsame_symm invEmpty)
  exact And.intro classified
    (And.intro productManifold
      (And.intro mulEmpty (And.intro invEmpty (And.intro mulUnary invUnary))))

theorem LieGroupSingleton_smooth_operation_readback
    {h k product mulChart invChart transition : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k -> Cont h k product ->
      Cont BHist.Empty product mulChart -> Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
        Cont mulChart invChart transition ->
          LieGroupSingletonClassifier product BHist.Empty ∧
            LieGroupSingletonClassifier (LieGroupSingletonInv h) BHist.Empty ∧
              hsame mulChart BHist.Empty ∧ hsame invChart BHist.Empty ∧
                hsame transition BHist.Empty ∧ UnaryHistory transition := by
  intro carrierH carrierK productRow mulChartRow invChartRow transitionRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productRow (cont_left_unit BHist.Empty)
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have productClassified : LieGroupSingletonClassifier product BHist.Empty :=
    And.intro productEmpty (And.intro emptyCarrier productEmpty)
  have invCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv h) := by
    rfl
  have invClassified : LieGroupSingletonClassifier (LieGroupSingletonInv h) BHist.Empty :=
    And.intro invCarrier (And.intro emptyCarrier invCarrier)
  have mulProduct : hsame mulChart product :=
    cont_left_unit_result mulChartRow
  have mulEmpty : hsame mulChart BHist.Empty :=
    hsame_trans mulProduct productEmpty
  have invEndpoint : hsame invChart (LieGroupSingletonInv h) :=
    cont_left_unit_result invChartRow
  have invEmpty : hsame invChart BHist.Empty :=
    hsame_trans invEndpoint invCarrier
  have transitionEmpty : hsame transition BHist.Empty :=
    cont_respects_hsame mulEmpty invEmpty transitionRow (cont_left_unit BHist.Empty)
  have transitionUnary : UnaryHistory transition :=
    unary_transport unary_empty (hsame_symm transitionEmpty)
  exact And.intro productClassified
    (And.intro invClassified
      (And.intro mulEmpty (And.intro invEmpty (And.intro transitionEmpty transitionUnary))))

theorem LieGroupSingleton_downstream_export {h k product chart : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k -> Cont h k product ->
      Cont BHist.Empty product chart ->
        LieGroupSingletonCarrier product ∧ LieGroupSingletonClassifier product BHist.Empty ∧
          ManifoldSingletonCarrier product ∧ hsame chart BHist.Empty ∧ UnaryHistory chart ∧
            (hsame product (BHist.e1 BHist.Empty) -> False) := by
  intro carrierH carrierK productRow chartRow
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productRow (cont_left_unit BHist.Empty)
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have classified : LieGroupSingletonClassifier product BHist.Empty :=
    And.intro productEmpty (And.intro emptyCarrier productEmpty)
  have productManifold : ManifoldSingletonCarrier product :=
    productEmpty
  have chartProduct : hsame chart product :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartProduct productEmpty
  have chartUnary : UnaryHistory chart :=
    unary_transport unary_empty (hsame_symm chartEmpty)
  have productNotSuccessor : hsame product (BHist.e1 BHist.Empty) -> False := by
    intro productSuccessor
    exact not_hsame_e1_empty (hsame_trans (hsame_symm productSuccessor) productEmpty)
  exact And.intro productEmpty
    (And.intro classified
      (And.intro productManifold
        (And.intro chartEmpty (And.intro chartUnary productNotSuccessor))))

theorem LieGroupSingleton_source_lock {h chart transition : BHist} :
    LieGroupSingletonCarrier h -> Cont BHist.Empty h chart -> Cont chart chart transition ->
      GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h ∧ LieGroupSingletonCarrier h ∧
        LieGroupSingletonClassifier h BHist.Empty ∧ hsame chart BHist.Empty ∧
          hsame transition BHist.Empty ∧ UnaryHistory chart ∧ UnaryHistory transition := by
  intro carrier chartRow transitionRow
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have classified : LieGroupSingletonClassifier h BHist.Empty :=
    And.intro carrier (And.intro emptyCarrier carrier)
  have chartH : hsame chart h :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartH carrier
  have transitionEmpty : hsame transition BHist.Empty :=
    cont_respects_hsame chartEmpty chartEmpty transitionRow (cont_left_unit BHist.Empty)
  have chartUnary : UnaryHistory chart :=
    unary_transport unary_empty (hsame_symm chartEmpty)
  have transitionUnary : UnaryHistory transition :=
    unary_transport unary_empty (hsame_symm transitionEmpty)
  exact And.intro carrier
    (And.intro carrier
      (And.intro carrier
        (And.intro classified
          (And.intro chartEmpty
            (And.intro transitionEmpty (And.intro chartUnary transitionUnary))))))

theorem LieGroupSingleton_exact_ledger {h k product chart : BHist} :
    LieGroupSingletonCarrier h -> LieGroupSingletonCarrier k -> Cont h k product ->
      Cont BHist.Empty product chart ->
        GroupSingletonCarrier h ∧ GroupSingletonCarrier k ∧ ManifoldSingletonCarrier product ∧
          LieGroupSingletonClassifier product BHist.Empty ∧ hsame chart BHist.Empty ∧
            UnaryHistory chart := by
  intro carrierH carrierK productRow chartRow
  have groupH : GroupSingletonCarrier h := carrierH
  have groupK : GroupSingletonCarrier k := carrierK
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productRow (cont_left_unit BHist.Empty)
  have productManifold : ManifoldSingletonCarrier product :=
    productEmpty
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have productClassified : LieGroupSingletonClassifier product BHist.Empty :=
    And.intro productEmpty (And.intro emptyCarrier productEmpty)
  have chartProduct : hsame chart product :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartProduct productEmpty
  have chartUnary : UnaryHistory chart :=
    unary_transport unary_empty (hsame_symm chartEmpty)
  exact And.intro groupH
    (And.intro groupK
      (And.intro productManifold
        (And.intro productClassified (And.intro chartEmpty chartUnary))))

theorem LieGroupSingleton_inverse_smooth_endomap {h invChart : BHist} :
    LieGroupSingletonCarrier h -> Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
      LieGroupSingletonCarrier (LieGroupSingletonInv h) ∧
        LieGroupSingletonClassifier (LieGroupSingletonInv (LieGroupSingletonInv h)) h ∧
          hsame invChart BHist.Empty ∧ UnaryHistory invChart := by
  intro carrierH invChartRow
  have invCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv h) := by
    rfl
  have doubleInvCarrier :
      LieGroupSingletonCarrier (LieGroupSingletonInv (LieGroupSingletonInv h)) := by
    rfl
  have doubleInvClassified :
      LieGroupSingletonClassifier (LieGroupSingletonInv (LieGroupSingletonInv h)) h :=
    And.intro doubleInvCarrier (And.intro carrierH (hsame_symm carrierH))
  have invChartEndpoint : hsame invChart (LieGroupSingletonInv h) :=
    cont_left_unit_result invChartRow
  have invChartEmpty : hsame invChart BHist.Empty :=
    invChartEndpoint
  exact And.intro invCarrier
    (And.intro doubleInvClassified
      (And.intro invChartEmpty (unary_transport unary_empty (hsame_symm invChartEmpty))))

theorem LieGroupSingleton_conjugation_smooth {s x sx conj chart : BHist} :
    LieGroupSingletonCarrier s -> LieGroupSingletonCarrier x -> Cont s x sx ->
      Cont sx (LieGroupSingletonInv s) conj -> Cont BHist.Empty conj chart ->
        LieGroupSingletonCarrier conj ∧ LieGroupSingletonClassifier conj BHist.Empty ∧
          hsame chart BHist.Empty ∧ UnaryHistory chart := by
  intro carrierS carrierX sxRow conjRow chartRow
  have sxCarrier : LieGroupSingletonCarrier sx := by
    have sxEmpty : hsame sx BHist.Empty :=
      cont_respects_hsame carrierS carrierX sxRow (cont_left_unit BHist.Empty)
    exact sxEmpty
  have invCarrier : LieGroupSingletonCarrier (LieGroupSingletonInv s) := by
    rfl
  have conjCarrier : LieGroupSingletonCarrier conj := by
    have conjEmpty : hsame conj BHist.Empty :=
      cont_respects_hsame sxCarrier invCarrier conjRow (cont_left_unit BHist.Empty)
    exact conjEmpty
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have conjClassified : LieGroupSingletonClassifier conj BHist.Empty :=
    And.intro conjCarrier (And.intro emptyCarrier conjCarrier)
  have chartConj : hsame chart conj :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartConj conjCarrier
  exact And.intro conjCarrier
    (And.intro conjClassified
      (And.intro chartEmpty (unary_transport unary_empty (hsame_symm chartEmpty))))

theorem LieGroupSingleton_conjugation_carrier_and_smoothness {s x chart : BHist} :
    LieGroupSingletonCarrier s -> LieGroupSingletonCarrier x ->
      Cont BHist.Empty (append (append s x) BHist.Empty) chart ->
        LieGroupSingletonCarrier (append (append s x) BHist.Empty) ∧
          LieGroupSingletonClassifier (append (append s x) BHist.Empty) BHist.Empty ∧
            ManifoldSingletonCarrier (append (append s x) BHist.Empty) ∧
              hsame chart BHist.Empty ∧ UnaryHistory chart := by
  intro carrierS carrierX chartRow
  have productEmpty : hsame (append s x) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierX)
  have conjugationEmpty : hsame (append (append s x) BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro productEmpty (hsame_refl BHist.Empty))
  have emptyCarrier : LieGroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have conjugationClassified :
      LieGroupSingletonClassifier (append (append s x) BHist.Empty) BHist.Empty :=
    And.intro conjugationEmpty (And.intro emptyCarrier conjugationEmpty)
  have conjugationManifold :
      ManifoldSingletonCarrier (append (append s x) BHist.Empty) :=
    conjugationEmpty
  have chartConjugation : hsame chart (append (append s x) BHist.Empty) :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartConjugation conjugationEmpty
  exact And.intro conjugationEmpty
    (And.intro conjugationClassified
      (And.intro conjugationManifold
        (And.intro chartEmpty (unary_transport unary_empty (hsame_symm chartEmpty)))))

theorem LieGroupSingleton_conjugation_action_law {s t x : BHist} :
    LieGroupSingletonCarrier s -> LieGroupSingletonCarrier t -> LieGroupSingletonCarrier x ->
      LieGroupSingletonClassifier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty)
        (append (append (append s t) x) BHist.Empty) := by
  intro carrierS carrierT carrierX
  have txEmpty : hsame (append t x) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierT carrierX)
  have txTailEmpty : hsame (append (append t x) BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro txEmpty (hsame_refl BHist.Empty))
  have leftInnerEmpty :
      hsame (append s (append (append t x) BHist.Empty)) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierS txTailEmpty)
  have leftCarrier :
      LieGroupSingletonCarrier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro leftInnerEmpty (hsame_refl BHist.Empty))
  have stEmpty : hsame (append s t) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierT)
  have rightInnerEmpty : hsame (append (append s t) x) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro stEmpty carrierX)
  have rightCarrier :
      LieGroupSingletonCarrier (append (append (append s t) x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro rightInnerEmpty (hsame_refl BHist.Empty))
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem LieGroupSingleton_adjoint_readback {s tangent chart : BHist} :
    LieGroupSingletonCarrier s ->
      BEDC.Derived.LieAlgebraUp.LieAlgebraSingletonCarrier tangent ->
        Cont BHist.Empty tangent chart ->
          BEDC.Derived.LieAlgebraUp.LieAlgebraSingletonCarrier chart ∧
            hsame chart BHist.Empty ∧ UnaryHistory chart := by
  intro carrierS tangentCarrier chartRow
  have singletonEndpoint : hsame (append s tangent) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierS tangentCarrier)
  have tangentEmpty : hsame tangent BHist.Empty :=
    (append_eq_empty_iff.mp singletonEndpoint).right
  have chartTangent : hsame chart tangent :=
    cont_left_unit_result chartRow
  have chartEmpty : hsame chart BHist.Empty :=
    hsame_trans chartTangent tangentEmpty
  exact And.intro chartEmpty
    (And.intro chartEmpty (unary_transport unary_empty (hsame_symm chartEmpty)))

end BEDC.Derived.LieGroupUp
