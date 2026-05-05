import BEDC.Derived.ContinuousUp.Transport

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def ContinuousPatternSpec
    (source f middle g target fg modF modG modFG certF certG cert : BHist) : Prop :=
  ContinuousFunctionCarrier source f middle modF certF ∧
    ContinuousFunctionCarrier middle g target modG certG ∧
      Cont f g fg ∧ Cont modF modG modFG ∧ Cont target modFG cert

theorem ContinuousPatternSpec_comp_carrier
    {source f middle g target fg modF modG modFG certF certG cert : BHist} :
    ContinuousPatternSpec source f middle g target fg modF modG modFG certF certG cert ->
      ContinuousFunctionCarrier source fg target modFG cert := by
  intro spec
  exact
    ContinuousFunctionCarrier_comp_closed spec.left spec.right.left spec.right.right.left
      spec.right.right.right.left spec.right.right.right.right

def ContinuousClassifierSpec
    (source source' map map' target target' modulus modulus' cert cert' : BHist) : Prop :=
  ContinuousFunctionCarrier source map target modulus cert ∧
    ContinuousFunctionCarrier source' map' target' modulus' cert' ∧
      hsame source source' ∧ hsame map map' ∧ hsame modulus modulus'

theorem ContinuousClassifierSpec_target_cert_readback
    {source source' map map' target target' modulus modulus' cert cert' : BHist} :
    ContinuousClassifierSpec source source' map map' target target' modulus modulus' cert cert' ->
      hsame target target' ∧ hsame cert cert' := by
  intro spec
  have transported :
      ContinuousFunctionCarrier source map target' modulus cert' :=
    ContinuousFunctionCarrier_hsame_transport
      (hsame_symm spec.right.right.left)
      (hsame_symm spec.right.right.right.left)
      (hsame_refl target')
      (hsame_symm spec.right.right.right.right)
      (hsame_refl cert')
      spec.right.left
  exact ContinuousFunctionCarrier_target_cert_deterministic spec.left transported

end BEDC.Derived.ContinuousUp
