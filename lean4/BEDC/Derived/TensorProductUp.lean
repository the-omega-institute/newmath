import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.Derived.ModuleUp

namespace BEDC.Derived.TensorProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.ModuleUp

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
