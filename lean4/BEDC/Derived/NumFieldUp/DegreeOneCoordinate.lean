import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldReflexiveRational_degree_one_coordinate_transport
    {h coord product : BHist} :
    NumFieldRatReflexiveCarrier h -> Cont h BHist.Empty coord ->
      Cont h (BHist.e1 BHist.Empty) product ->
        RatHistoryClassifier coord h ∧
          RatHistoryClassifier product
            (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) ∧
            RatHistoryCarrier coord ∧ RatHistoryCarrier product := by
  intro carrier coordinateReadback productReadback
  have coordH : hsame coord h :=
    cont_right_unit_result coordinateReadback
  have coordCarrier : RatHistoryCarrier coord :=
    RatHistoryCarrier_hsame_transport (hsame_symm coordH) carrier.left
  have coordClassifier : RatHistoryClassifier coord h :=
    And.intro coordCarrier (And.intro carrier.left coordH)
  have sourceClassified : RatHistoryClassifier h (FieldExtSingletonEmbedding h) :=
    RatHistoryLedgerPolicy_raw_visible_classifier carrier.right.right.left
  have basisUnary : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have productClassifiedRaw :
      RatHistoryClassifier (append h (BHist.e1 BHist.Empty))
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_append_unary_denominator_closed sourceClassified basisUnary
      (hsame_refl (BHist.e1 BHist.Empty))
  have productClassified :
      RatHistoryClassifier product
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    RatHistoryClassifier_hsame_transport (hsame_symm productReadback)
      (hsame_refl (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)))
      productClassifiedRaw
  exact And.intro coordClassifier
    (And.intro productClassified (And.intro coordCarrier productClassified.left))

end BEDC.Derived.NumFieldUp
