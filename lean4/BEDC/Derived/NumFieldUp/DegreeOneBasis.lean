import BEDC.Derived.NumFieldUp

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldRatReflexive_degree_one_basis_exhaustion {h basis coord : BHist} :
    NumFieldRatReflexiveCarrier h -> RatHistoryCarrier basis ->
      hsame basis (BHist.e1 BHist.Empty) -> Cont h basis coord ->
        RatHistoryCarrier (BHist.e1 BHist.Empty) ∧
          RatHistoryClassifier coord (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) ∧
            RatHistoryCarrier coord ∧ Cont h basis coord := by
  intro carrier basisCarrier sameBasis coordinateContinuation
  have endpointCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) :=
    RatHistoryCarrier_e1_tail_unary_iff.mpr unary_empty
  have coordinateClassified :
      RatHistoryClassifier coord (append (FieldExtSingletonEmbedding h) (BHist.e1 BHist.Empty)) :=
    NumFieldReflexiveRational_singleton_basis_transport carrier basisCarrier sameBasis
      coordinateContinuation
  exact And.intro endpointCarrier
    (And.intro coordinateClassified
      (And.intro coordinateClassified.left coordinateContinuation))

end BEDC.Derived.NumFieldUp
