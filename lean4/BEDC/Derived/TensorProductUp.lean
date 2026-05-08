import BEDC.Derived.ModuleUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TensorProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ModuleUp

def TensorProductSingletonCarrier (h : BHist) : Prop :=
  exists l : BHist, exists r : BHist, ModuleSingletonCarrier l ∧
    ModuleSingletonCarrier r ∧ Cont l r h

theorem TensorProductSingletonCarrier_empty_endpoint_iff {h : BHist} :
    TensorProductSingletonCarrier h ↔ hsame h BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro left leftRest =>
        cases leftRest with
        | intro right data =>
            cases data with
            | intro leftCarrier tail =>
                cases tail with
                | intro rightCarrier continuation =>
                    cases leftCarrier
                    cases rightCarrier
                    cases continuation
                    rfl
  · intro sameEmpty
    cases sameEmpty
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (cont_left_unit BHist.Empty))))

theorem TensorProductSingletonCarrier_continuation_suffix_carrier {pair suffix out : BHist} :
    TensorProductSingletonCarrier pair -> Cont pair suffix out ->
      TensorProductSingletonCarrier out -> ModuleSingletonCarrier suffix := by
  intro pairCarrier pairSuffix outCarrier
  cases pairCarrier with
  | intro left pairRest =>
      cases pairRest with
      | intro right pairData =>
          cases pairData with
          | intro leftCarrier pairTail =>
              cases pairTail with
              | intro rightCarrier pairCont =>
                  cases outCarrier with
                  | intro outLeft outRest =>
                      cases outRest with
                      | intro outRight outData =>
                          cases outData with
                          | intro outLeftCarrier outTail =>
                              cases outTail with
                              | intro outRightCarrier outCont =>
                                  cases leftCarrier
                                  cases rightCarrier
                                  cases pairCont
                                  cases outLeftCarrier
                                  cases outRightCarrier
                                  cases outCont
                                  exact (append_eq_empty_iff.mp pairSuffix.symm).right

theorem TensorProductSingletonCarrier_continuation_prefix_carrier {pre pair out : BHist} :
    TensorProductSingletonCarrier pair -> Cont pre pair out ->
      TensorProductSingletonCarrier out -> ModuleSingletonCarrier pre := by
  intro pairCarrier prefixPair outCarrier
  have pairEmpty : hsame pair BHist.Empty :=
    TensorProductSingletonCarrier_empty_endpoint_iff.mp pairCarrier
  have outEmpty : hsame out BHist.Empty :=
    TensorProductSingletonCarrier_empty_endpoint_iff.mp outCarrier
  cases pairEmpty
  cases outEmpty
  exact (cont_empty_result_inversion prefixPair).left

theorem TensorProductSingletonCarrier_result_empty_continuation {tensor : BHist} :
    TensorProductSingletonCarrier tensor -> Cont tensor BHist.Empty BHist.Empty := by
  intro carrier
  cases carrier with
  | intro l rest =>
      cases rest with
      | intro r data =>
          cases data with
          | intro lCarrier tail =>
              cases tail with
              | intro rCarrier cont =>
                  cases lCarrier
                  cases rCarrier
                  cases cont
                  rfl

open BEDC.FKernel.NameCert

theorem TensorProductSingletonCarrier_empty_iff {h : BHist} :
    TensorProductSingletonCarrier h ↔ hsame h BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro left rest =>
        cases rest with
        | intro right data =>
            exact cont_respects_hsame data.left data.right.left data.right.right
              (cont_right_unit BHist.Empty)
  · intro emptyH
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty)
            (cont_result_hsame_transport (cont_right_unit BHist.Empty) (hsame_symm emptyH)))))

theorem TensorProductSingletonCarrier_continuation_result_closed {pair suffix out : BHist} :
    TensorProductSingletonCarrier pair -> ModuleSingletonCarrier suffix -> Cont pair suffix out ->
      TensorProductSingletonCarrier out := by
  intro pairCarrier suffixCarrier pairSuffix
  have pairEmpty : hsame pair BHist.Empty :=
    TensorProductSingletonCarrier_empty_iff.mp pairCarrier
  have moved : Cont BHist.Empty BHist.Empty out :=
    cont_hsame_transport pairEmpty suffixCarrier (hsame_refl out) pairSuffix
  have outEmpty : hsame out BHist.Empty := cont_left_unit_result moved
  exact TensorProductSingletonCarrier_empty_iff.mpr outEmpty

def TensorProductSingletonFactor (left right tensor : BHist) : Prop :=
  ModuleSingletonCarrier left ∧ ModuleSingletonCarrier right ∧
    ModuleSingletonCarrier tensor ∧ Cont left right tensor

theorem TensorProductSingletonFactor_classifier_uniqueness {left right tensor tensor' : BHist} :
    TensorProductSingletonFactor left right tensor ->
      TensorProductSingletonFactor left right tensor' ->
        hsame tensor tensor' ∧ Cont left right tensor ∧ Cont left right tensor' := by
  intro leftFactor rightFactor
  have leftCont : Cont left right tensor := leftFactor.right.right.right
  have rightCont : Cont left right tensor' := rightFactor.right.right.right
  exact And.intro (cont_deterministic leftCont rightCont) (And.intro leftCont rightCont)

theorem TensorProductSingletonCarrier_factor_witness {tensor : BHist} :
    TensorProductSingletonCarrier tensor ->
      Exists (fun left : BHist => Exists (fun right : BHist =>
        TensorProductSingletonFactor left right tensor ∧ Cont left right tensor)) := by
  intro carrier
  cases carrier with
  | intro left leftRest =>
      cases leftRest with
      | intro right data =>
          cases data with
          | intro leftCarrier tail =>
              cases tail with
              | intro rightCarrier continuation =>
                  cases leftCarrier
                  cases rightCarrier
                  cases continuation
                  exact Exists.intro BHist.Empty
                    (Exists.intro BHist.Empty
                      (And.intro
                        (And.intro (hsame_refl BHist.Empty)
                          (And.intro (hsame_refl BHist.Empty)
                            (And.intro (hsame_refl BHist.Empty)
                              (cont_left_unit BHist.Empty))))
                        (cont_left_unit BHist.Empty)))

theorem TensorProductSingletonCarrier_source_pattern_iff {tensor : BHist} :
    TensorProductSingletonCarrier tensor ↔
      exists left right : BHist,
        TensorProductSingletonFactor left right tensor ∧ Cont left right tensor := by
  constructor
  · intro carrier
    exact TensorProductSingletonCarrier_factor_witness carrier
  · intro witness
    cases witness with
    | intro left rest =>
        cases rest with
        | intro right data =>
            exact Exists.intro left
              (Exists.intro right
                (And.intro data.left.left
                  (And.intro data.left.right.left data.right)))

theorem TensorProductSingletonFactor_hsame_transport
    {left left' right right' tensor tensor' : BHist} :
    TensorProductSingletonFactor left right tensor ->
      hsame left left' -> hsame right right' -> hsame tensor tensor' ->
        TensorProductSingletonFactor left' right' tensor' ∧ Cont left' right' tensor' := by
  intro factor sameLeft sameRight sameTensor
  have leftCarrier' : ModuleSingletonCarrier left' :=
    hsame_trans (hsame_symm sameLeft) factor.left
  have rightCarrier' : ModuleSingletonCarrier right' :=
    hsame_trans (hsame_symm sameRight) factor.right.left
  have tensorCarrier' : ModuleSingletonCarrier tensor' :=
    hsame_trans (hsame_symm sameTensor) factor.right.right.left
  have tensorCont' : Cont left' right' tensor' :=
    cont_hsame_transport sameLeft sameRight sameTensor factor.right.right.right
  exact And.intro
      (And.intro leftCarrier'
        (And.intro rightCarrier' (And.intro tensorCarrier' tensorCont')))
    tensorCont'

theorem TensorProductSingletonFactor_source_target_swap {left right tensor : BHist} :
    TensorProductSingletonFactor left right tensor ->
      TensorProductSingletonFactor right left tensor ∧ Cont right left tensor := by
  intro factor
  exact TensorProductSingletonFactor_hsame_transport factor
    (hsame_trans factor.left (hsame_symm factor.right.left))
    (hsame_trans factor.right.left (hsame_symm factor.left))
    (hsame_refl tensor)

theorem TensorProductSingletonFactor_associator {l r s t u : BHist} :
    TensorProductSingletonFactor l r t -> TensorProductSingletonFactor t s u ->
      exists m : BHist, TensorProductSingletonFactor r s m ∧
        TensorProductSingletonFactor l m u ∧ Cont r s m ∧ Cont l m u := by
  intro leftFactor rightFactor
  have assoc := cont_assoc_left_exists leftFactor.right.right.right rightFactor.right.right.right
  cases assoc with
  | intro m conts =>
      have mCarrier : ModuleSingletonCarrier m :=
        @cont_left_unit_result BHist.Empty m
          (@cont_hsame_transport r BHist.Empty s BHist.Empty m m
            leftFactor.right.left rightFactor.right.left (hsame_refl m) conts.left)
      exact Exists.intro m
        (And.intro
          (And.intro leftFactor.right.left
            (And.intro rightFactor.right.left (And.intro mCarrier conts.left)))
            (And.intro
              (And.intro leftFactor.left
                (And.intro mCarrier (And.intro rightFactor.right.right.left conts.right)))
            (And.intro conts.left conts.right)))

theorem TensorProductSingletonFactor_classifier_uniqueness_readback {l r t t' : BHist} :
    TensorProductSingletonFactor l r t -> TensorProductSingletonFactor l r t' ->
      hsame t t' ∧ Cont l r t ∧ Cont l r t' := by
  intro leftFactor rightFactor
  have sameTensor : hsame t t' :=
    cont_deterministic leftFactor.right.right.right rightFactor.right.right.right
  exact And.intro sameTensor
    (And.intro leftFactor.right.right.right rightFactor.right.right.right)

theorem TensorProductSingletonFactor_tensor_semanticNameCert {left right tensor : BHist} :
    TensorProductSingletonFactor left right tensor ->
      SemanticNameCert (fun t : BHist => TensorProductSingletonFactor left right t)
        (fun t : BHist => TensorProductSingletonFactor left right t)
        (fun t : BHist => TensorProductSingletonFactor left right t) hsame := by
  intro factor
  constructor
  · constructor
    · exact Exists.intro tensor factor
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      exact (TensorProductSingletonFactor_hsame_transport carrierH
        (hsame_refl left) (hsame_refl right) same).left
  · intro h source
    exact source
  · intro h source
    exact source

theorem TensorProductSingletonFactor_classifier_stability_obligation
    {left left' right right' tensor tensor' : BHist} :
    TensorProductSingletonFactor left right tensor ->
      hsame left left' -> hsame right right' -> hsame tensor tensor' ->
        TensorProductSingletonFactor left' right' tensor' ∧ Cont left' right' tensor' ∧
          SemanticNameCert (fun t : BHist => TensorProductSingletonFactor left' right' t)
            (fun t : BHist => TensorProductSingletonFactor left' right' t)
            (fun t : BHist => TensorProductSingletonFactor left' right' t) hsame := by
  intro factor sameLeft sameRight sameTensor
  have transported :=
    TensorProductSingletonFactor_hsame_transport factor sameLeft sameRight sameTensor
  exact And.intro transported.left
    (And.intro transported.right
      (TensorProductSingletonFactor_tensor_semanticNameCert transported.left))

theorem TensorProductSingletonFactor_ledger_exactness_obligation {left right tensor : BHist} :
    TensorProductSingletonFactor left right tensor ->
      ModuleSingletonCarrier left ∧ ModuleSingletonCarrier right ∧
        ModuleSingletonCarrier tensor ∧ Cont left right tensor ∧
          (forall {tensor' : BHist}, TensorProductSingletonFactor left right tensor' ->
            hsame tensor tensor') := by
  intro factor
  exact And.intro factor.left
    (And.intro factor.right.left
      (And.intro factor.right.right.left
        (And.intro factor.right.right.right
          (by
            intro tensor' factor'
            exact (TensorProductSingletonFactor_classifier_uniqueness factor factor').left))))

end BEDC.Derived.TensorProductUp
