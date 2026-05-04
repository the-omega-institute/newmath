import BEDC.Derived.GroupUp.SingletonNormalizerAction

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.MonoidUp

theorem FullUnaryAppendInverse_obstruction (inv : BHist → BHist)
    (inverseLaw : ∀ h : BHist, UnaryHistory h →
      UnaryHistory (inv h) ∧
        MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) :
    False := by
  have oneUnary : UnaryHistory (BHist.e1 BHist.Empty) := unary_e1_closed unary_empty
  have productClassified :
      MonoidHistoryClassifier UnaryHistory
        (append (BHist.e1 BHist.Empty) (inv (BHist.e1 BHist.Empty))) BHist.Empty :=
    (inverseLaw (BHist.e1 BHist.Empty) oneUnary).right
  have factors :=
    unary_append_unit_product_factor_exactness.mp productClassified
  exact not_hsame_e1_empty factors.left.right.right

theorem UnaryHistory_append_inverse_obstruction {inv : BHist -> BHist} :
    (forall h : BHist, UnaryHistory h -> UnaryHistory (inv h) ∧
      MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) -> False := by
  intro inverseLaw
  have visibleUnary : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have productClassified :
      MonoidHistoryClassifier UnaryHistory
        (append (BHist.e1 BHist.Empty) (inv (BHist.e1 BHist.Empty))) BHist.Empty :=
    (inverseLaw (BHist.e1 BHist.Empty) visibleUnary).right
  have factors :=
    (MonoidHistoryClassifier_unary_append_unit_product_factor_exactness
      (h := BHist.e1 BHist.Empty) (k := inv (BHist.e1 BHist.Empty))).mp productClassified
  exact not_hsame_e1_empty factors.left.right.right

theorem unary_append_inverse_field_singleton_collapse_iff (inv : BHist -> BHist) :
    (∀ h : BHist, UnaryHistory h -> UnaryHistory (inv h)) ->
      (((∀ h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) ∧
        (∀ h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory (append (inv h) h) BHist.Empty)) <->
        (∀ h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory h BHist.Empty)) := by
  intro inverseUnary
  constructor
  · intro inverseFields h unaryH
    exact (unary_append_unit_product_factor_exactness.mp
      (inverseFields.left h unaryH)).left
  · intro collapse
    constructor
    · intro h unaryH
      exact unary_append_unit_product_factor_exactness.mpr
        (And.intro (collapse h unaryH) (collapse (inv h) (inverseUnary h unaryH)))
    · intro h unaryH
      exact unary_append_unit_product_factor_exactness.mpr
        (And.intro (collapse (inv h) (inverseUnary h unaryH)) (collapse h unaryH))

protected theorem unary_append_inverse_field_collapses_to_singleton (inv : BHist -> BHist) :
    (forall h : BHist, UnaryHistory h ->
      MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) ->
    (forall h : BHist, UnaryHistory h ->
      MonoidHistoryClassifier UnaryHistory h BHist.Empty) := by
  intro inverseField h hUnary
  have productClassified :
      MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty :=
    inverseField h hUnary
  have factors :=
    (MonoidHistoryClassifier_unary_append_unit_product_factor_exactness
      (h := h) (k := inv h)).mp productClassified
  exact factors.left

theorem unary_append_inverse_field_iff_singleton_collapse {inv : BHist -> BHist} :
    (forall h : BHist, UnaryHistory h -> UnaryHistory (inv h)) ->
      (((forall h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) ∧
        (forall h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory (append (inv h) h) BHist.Empty)) <->
        (forall h : BHist, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory h BHist.Empty)) := by
  intro invUnary
  constructor
  · intro inverseLaws
    exact
      BEDC.Derived.GroupUp.unary_append_inverse_field_collapses_to_singleton inv
        inverseLaws.left
  · intro singletonCollapse
    constructor
    · intro h hUnary
      have hClassified : MonoidHistoryClassifier UnaryHistory h BHist.Empty :=
        singletonCollapse h hUnary
      have invUnaryH : UnaryHistory (inv h) := invUnary h hUnary
      have invClassified : MonoidHistoryClassifier UnaryHistory (inv h) BHist.Empty :=
        singletonCollapse (inv h) invUnaryH
      exact
        (MonoidHistoryClassifier_unary_append_unit_product_factor_exactness
          (h := h) (k := inv h)).mpr
          (And.intro hClassified invClassified)
    · intro h hUnary
      have hClassified : MonoidHistoryClassifier UnaryHistory h BHist.Empty :=
        singletonCollapse h hUnary
      have invUnaryH : UnaryHistory (inv h) := invUnary h hUnary
      have invClassified : MonoidHistoryClassifier UnaryHistory (inv h) BHist.Empty :=
        singletonCollapse (inv h) invUnaryH
      exact
        (MonoidHistoryClassifier_unary_append_unit_product_factor_exactness
          (h := inv h) (k := h)).mpr
          (And.intro invClassified hClassified)

end BEDC.Derived.GroupUp
