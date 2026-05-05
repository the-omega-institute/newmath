import BEDC.Derived.FieldUp.ProductApartness
import BEDC.FKernel.Cont.Cancellation

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

theorem FieldApartTailFactor_empty_context_hsame_transport
    {l l' h h' r r' u u' v v' : BHist} :
    Cont l h u -> Cont u r v -> hsame l BHist.Empty -> hsame r BHist.Empty ->
      hsame l l' -> hsame h h' -> hsame r r' -> hsame u u' -> hsame v v' ->
        FieldApartTailFactor v' h' := by
  intro leftCont rightCont leftEmpty rightEmpty sameL sameH sameR sameU sameV
  have leftCont' : Cont l' h' u' :=
    cont_hsame_transport sameL sameH sameU leftCont
  have rightCont' : Cont u' r' v' :=
    cont_hsame_transport sameU sameR sameV rightCont
  have leftEmpty' : hsame l' BHist.Empty :=
    hsame_trans (hsame_symm sameL) leftEmpty
  have rightEmpty' : hsame r' BHist.Empty :=
    hsame_trans (hsame_symm sameR) rightEmpty
  exact FieldApartTailFactor.emptyContext leftCont' rightCont' leftEmpty' rightEmpty'

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

theorem FieldApartTailFactor_empty_endpoint_exclusion_hsame_transport {y x y' x' : BHist} :
    FieldApartTailFactor y x -> hsame y y' -> hsame x x' -> hsame y' BHist.Empty ->
      FieldApartZero x' -> False := by
  intro factor sameY sameX endpoint apart
  cases sameY
  cases sameX
  exact FieldApartTailFactor_empty_endpoint_exclusion factor endpoint apart

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

theorem FieldApartTailFactor_continuation_hsame_closure {w w' x x' q z : BHist} :
    FieldApartTailFactor w x -> hsame w w' -> hsame x x' -> Cont w' q z ->
      FieldApartTailFactor z x' := by
  intro factor sameW sameX continuation
  cases sameW
  cases sameX
  exact FieldApartTailFactor.carriedTail factor continuation

theorem FieldApartTailFactor_singleton_context_exclusion {L R y x endpoint : BHist} :
    FieldSingletonCarrier L -> FieldSingletonCarrier R -> FieldApartTailFactor y x ->
      FieldSingletonClassifier (append L y) (append R endpoint) -> FieldApartZero x ->
        False := by
  intro carrierL carrierR factor classified apartX
  have exposed : FieldSingletonClassifier y endpoint :=
    Iff.mp (FieldSingletonClassifier_append_context_cancel_iff carrierL carrierR) classified
  exact FieldApartTailFactor_empty_endpoint_exclusion factor exposed.left apartX

theorem FieldApartTailFactor_hsame_transport_continuation_package {y y' x x' : BHist} :
    FieldApartTailFactor y x -> hsame y y' -> hsame x x' ->
      FieldApartTailFactor y' x' ∧
        (forall {q z : BHist}, Cont y' q z -> FieldApartTailFactor z x') := by
  intro factor sameY sameX
  induction factor generalizing y' x' with
  | emptyContext leftCont rightCont leftEmpty rightEmpty =>
      have transportedFactor :
          FieldApartTailFactor y' x' :=
        FieldApartTailFactor_empty_context_hsame_transport leftCont rightCont leftEmpty rightEmpty
          (hsame_refl _) sameX (hsame_refl _) (hsame_refl _) sameY
      exact
        ⟨transportedFactor,
          fun continuation => FieldApartTailFactor.carriedTail transportedFactor continuation⟩
  | carriedTail factor tailCont ih =>
      cases sameY
      cases sameX
      have transportedFactor : FieldApartTailFactor _ _ :=
        FieldApartTailFactor.carriedTail factor tailCont
      exact
        ⟨transportedFactor,
          fun continuation => FieldApartTailFactor.carriedTail transportedFactor continuation⟩
  | exposedFactor tailCont =>
      cases sameY
      cases sameX
      have transportedFactor : FieldApartTailFactor _ _ :=
        FieldApartTailFactor.exposedFactor tailCont
      exact
        ⟨transportedFactor,
          fun continuation => FieldApartTailFactor.carriedTail transportedFactor continuation⟩

end BEDC.Derived.FieldUp
