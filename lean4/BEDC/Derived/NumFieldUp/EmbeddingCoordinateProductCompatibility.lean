import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldRatReflexive_embedding_coordinate_product_compatibility
    {m coord product action : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      Cont m (BHist.e1 BHist.Empty) product ->
        Cont (FieldExtSingletonEmbedding m) (BHist.e1 BHist.Empty) action ->
          RatHistoryClassifier coord m ∧ RatHistoryClassifier product action ∧
            RatHistoryCarrier product ∧ RatHistoryCarrier action ∧
              RatHistoryClassifier (FieldExtSingletonEmbedding m) coord := by
  intro carrierM coordinateReadback productCont actionCont
  have coordRows :=
    NumFieldReflexiveRational_finite_extension_witness carrierM coordinateReadback
  have basisCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr BEDC.FKernel.Unary.unary_empty
  have operationRows :
      RatHistoryClassifier product action ∧ RatHistoryCarrier product ∧
        RatHistoryCarrier action ∧ RatHistoryClassifier (FieldExtSingletonEmbedding m) m :=
    FieldExtRatReflexive_operation_table_source_coverage
      (And.intro carrierM (And.intro carrierM (hsame_refl m)))
      (And.intro basisCarrier (And.intro basisCarrier (hsame_refl (BHist.e1 BHist.Empty))))
      productCont actionCont
  have embeddingCoord : RatHistoryClassifier (FieldExtSingletonEmbedding m) coord :=
    RatHistoryClassifier_trans coordRows.right.right (RatHistoryClassifier_symm coordRows.left)
  exact And.intro coordRows.left
    (And.intro operationRows.left
      (And.intro operationRows.right.left
        (And.intro operationRows.right.right.left embeddingCoord)))

end BEDC.Derived.NumFieldUp
