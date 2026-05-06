import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldRatReflexiveSingletonBasisRow_support_exactness
    {h coord support : BHist} :
    NumFieldRatReflexiveSingletonBasisRow h coord support ->
      hsame support BHist.Empty ∧ (RatHistoryCarrier support -> False) ∧
        NumFieldRatReflexiveCarrier h ∧ Cont h BHist.Empty coord ∧
          RatHistoryClassifier coord h ∧
            RatHistoryClassifier (FieldExtSingletonEmbedding h) h := by
  intro row
  have supportEmptyEq : support = BHist.Empty := row.left
  have supportEmpty : hsame support BHist.Empty := supportEmptyEq
  have supportNonRat : RatHistoryCarrier support -> False := by
    intro supportCarrier
    exact RatHistoryCarrier_not_empty supportCarrier supportEmpty
  have carrier : NumFieldRatReflexiveCarrier h := row.right.left
  have coordReadback : Cont h BHist.Empty coord := row.right.right.left
  have coordClassified : RatHistoryClassifier coord h := row.right.right.right.left
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding h) :=
    row.right.right.right.right
  have embeddedClassified : RatHistoryClassifier (FieldExtSingletonEmbedding h) h :=
    And.intro embeddedCarrier (And.intro carrier.left (cont_left_unit_result carrier.right.right.right))
  exact And.intro supportEmpty
    (And.intro supportNonRat
      (And.intro carrier
        (And.intro coordReadback (And.intro coordClassified embeddedClassified))))

end BEDC.Derived.NumFieldUp
