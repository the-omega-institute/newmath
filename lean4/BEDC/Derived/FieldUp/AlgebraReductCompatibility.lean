import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem RatUpFieldUp_algebra_reduct_compatibility :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
      FieldSingletonClassifier ∧
      (forall {u : BHist},
        ((forall {d r : BHist}, RatHistoryCarrier d -> Cont u d r ->
          RatHistoryClassifier r d) <-> hsame u BHist.Empty)) ∧
      (forall {h : BHist}, FieldSingletonNonZero h -> False) := by
  exact And.intro singleton_empty_history_field_schema_laws.left
    (And.intro field_rat_denominator_continuation_left_unit_law_endpoint_empty_iff
      FieldSingletonNonZero_absurd)

end BEDC.Derived.FieldUp
