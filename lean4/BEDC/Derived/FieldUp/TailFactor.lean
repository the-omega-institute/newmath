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

end BEDC.Derived.FieldUp
