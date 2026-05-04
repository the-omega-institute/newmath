import BEDC.Derived.GroupUp
import BEDC.Derived.MonoidUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem unary_append_inverse_obstruction (inv : BHist -> BHist)
    (inverseLaw :
      forall h : BHist, UnaryHistory h ->
        UnaryHistory (inv h) ∧
          BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
            (append h (inv h)) BHist.Empty) :
    False := by
  have unaryOne : UnaryHistory (BHist.e1 BHist.Empty) := unary_empty
  have productClassified :
      BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
        (append (BHist.e1 BHist.Empty) (inv (BHist.e1 BHist.Empty))) BHist.Empty :=
    (inverseLaw (BHist.e1 BHist.Empty) unaryOne).right
  have split :=
    BEDC.Derived.MonoidUp.unary_append_unit_product_factor_exactness.mp
      productClassified
  exact not_hsame_e1_empty split.left.right.right

theorem unary_append_left_inverse_field_obstruction (inv : BHist -> BHist)
    (inverseLaw :
      forall h : BHist, UnaryHistory h ->
        UnaryHistory (inv h) ∧
          BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
            (append (inv h) h) BHist.Empty) :
    False := by
  have unaryOne : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have productClassified :
      BEDC.Derived.MonoidUp.MonoidHistoryClassifier UnaryHistory
        (append (inv (BHist.e1 BHist.Empty)) (BHist.e1 BHist.Empty)) BHist.Empty :=
    (inverseLaw (BHist.e1 BHist.Empty) unaryOne).right
  have split :=
    BEDC.Derived.MonoidUp.unary_append_unit_product_factor_exactness.mp
      productClassified
  exact not_hsame_e1_empty split.right.right.right

end BEDC.Derived.GroupUp
