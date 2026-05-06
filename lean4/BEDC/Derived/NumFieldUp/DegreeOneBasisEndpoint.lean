import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldRatReflexive_degree_one_basis_endpoint {h basis coord : BHist} :
    NumFieldRatReflexiveCarrier h -> hsame basis (BHist.e1 BHist.Empty) ->
      Cont h basis coord ->
        RatHistoryCarrier basis ∧ PositiveUnaryDenominator basis ∧
          RatHistoryClassifier coord (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) := by
  intro carrier sameBasis coordinateRow
  have basisCarrier : RatHistoryCarrier basis :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameBasis)
      (RatHistoryCarrier_iff_positive_denominator.mpr
        (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty))
  have positiveBasis : PositiveUnaryDenominator basis :=
    RatHistoryCarrier_iff_positive_denominator.mp basisCarrier
  have coordClassified :
      RatHistoryClassifier coord
        (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    NumFieldReflexiveRational_singleton_basis_transport carrier basisCarrier sameBasis
      coordinateRow
  exact And.intro basisCarrier (And.intro positiveBasis coordClassified)

end BEDC.Derived.NumFieldUp
