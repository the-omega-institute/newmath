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

theorem FullUnaryAppendLeftInverse_obstruction (inv : BHist -> BHist)
    (inverseLaw : forall h : BHist, UnaryHistory h ->
      UnaryHistory (inv h) ∧
        MonoidHistoryClassifier UnaryHistory (BEDC.FKernel.Cont.append (inv h) h) BHist.Empty) :
    False := by
  have oneUnary : UnaryHistory (BHist.e1 BHist.Empty) := unary_e1_closed unary_empty
  have productClassified :
      MonoidHistoryClassifier UnaryHistory
        (append (inv (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty)) BHist.Empty :=
    (inverseLaw (BHist.e1 BHist.Empty) oneUnary).right
  have factors :=
    unary_append_unit_product_factor_exactness.mp productClassified
  exact not_hsame_e1_empty factors.right.right.right

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

end BEDC.Derived.GroupUp
