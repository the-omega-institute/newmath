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

def TensorProductSingletonFactor (left right tensor : BHist) : Prop :=
  ModuleSingletonCarrier left ∧ ModuleSingletonCarrier right ∧
    ModuleSingletonCarrier tensor ∧ Cont left right tensor

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

end BEDC.Derived.TensorProductUp
