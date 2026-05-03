import BEDC.Derived.FieldUp.ProductApartness

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive FieldApartTailFactor : BHist -> BHist -> Prop where
  | emptyContext {l h r u v : BHist} :
      Cont l h u -> Cont u r v -> hsame l BHist.Empty -> hsame r BHist.Empty ->
        FieldApartTailFactor v h
  | carriedTail {w x q z : BHist} :
      FieldApartTailFactor w x -> Cont w q z -> FieldApartTailFactor z x
  | exposedFactor {w q z : BHist} :
      Cont w q z -> FieldApartTailFactor z q

theorem FieldApartTailFactor_empty_endpoint_exclusion {y x : BHist} :
    FieldApartTailFactor y x -> hsame y BHist.Empty -> FieldApartZero x -> False := by
  intro factor
  induction factor with
  | emptyContext leftCont rightCont leftEmpty rightEmpty =>
      intro endpoint apart
      have nestedIff :=
        FieldApartZero_nested_continuation_empty_context_iff
          leftCont rightCont leftEmpty rightEmpty
      exact (Iff.mpr nestedIff apart) endpoint
  | carriedTail factor tailCont ih =>
      intro endpoint apart
      cases endpoint
      have split := cont_empty_result_inversion tailCont
      exact ih split.left apart
  | exposedFactor tailCont =>
      intro endpoint apart
      cases endpoint
      have split := cont_empty_result_inversion tailCont
      exact apart split.right

theorem FieldApartTailFactor_result_closure {y x : BHist} :
    FieldApartTailFactor y x -> FieldApartZero x -> FieldApartZero y := by
  intro factor
  induction factor with
  | emptyContext leftCont rightCont leftEmpty rightEmpty =>
      intro apart
      exact
        Iff.mpr
          (FieldApartZero_nested_continuation_empty_context_iff
            leftCont rightCont leftEmpty rightEmpty)
          apart
  | carriedTail factor tailCont ih =>
      intro apart
      exact
        Iff.mpr (FieldApartZero_continuation_endpoint_split_iff tailCont)
          (Or.inl (ih apart))
  | exposedFactor tailCont =>
      intro apart
      exact
        Iff.mpr (FieldApartZero_continuation_endpoint_split_iff tailCont)
          (Or.inr apart)

theorem FieldApartTailFactor_continuation_result_closure {w x q z : BHist} :
    FieldApartTailFactor w x -> Cont w q z -> FieldApartZero x -> FieldApartZero z := by
  intro factor continuation apart
  exact
    Iff.mpr (FieldApartZero_continuation_endpoint_split_iff continuation)
      (Or.inl (FieldApartTailFactor_result_closure factor apart))

theorem FieldApartTailFactor_singleton_context_exclusion {L R y x endpoint : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> FieldApartTailFactor y x ->
      FieldSingletonClassifier (append L y) (append R endpoint) -> FieldApartZero x ->
        False := by
  intro carrierL carrierR factor classified apartX
  have exposed : FieldSingletonClassifier y endpoint :=
    Iff.mp (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR) classified
  exact FieldApartTailFactor_empty_endpoint_exclusion factor exposed.left apartX

end BEDC.Derived.FieldUp
