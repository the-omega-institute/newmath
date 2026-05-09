import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.PinGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PinGroupReflectionParityCarrier
    (spin reflection product endpoint : BHist) : Prop :=
  (hsame endpoint spin ∧ UnaryHistory spin) ∨
    (Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection)

theorem PinGroupReflectionParityCarrier_stability
    {spin reflection product endpoint spin' reflection' product' endpoint' : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      hsame spin spin' ->
        hsame reflection reflection' ->
          hsame product product' ->
            hsame endpoint endpoint' ->
              Cont spin' reflection' product' ->
                PinGroupReflectionParityCarrier spin' reflection' product' endpoint' := by
  intro carrier sameSpin sameReflection sameProduct sameEndpoint productCont'
  cases carrier with
  | inl spinBranch =>
      exact Or.inl
        (And.intro
          (hsame_trans (hsame_symm sameEndpoint)
            (hsame_trans spinBranch.left sameSpin))
          (unary_transport spinBranch.right sameSpin))
  | inr reflectionBranch =>
      exact Or.inr
        (And.intro productCont'
          (And.intro
            (hsame_trans (hsame_symm sameEndpoint)
              (hsame_trans reflectionBranch.right.left sameProduct))
            (unary_transport reflectionBranch.right.right sameReflection)))

theorem PinGroupReflectionParityCarrier_exactness
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      Cont endpoint ledger carried ->
        (hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
          (hsame carried (append product ledger) ∧
            Cont spin reflection product ∧ UnaryHistory reflection) := by
  intro carrier endpointLedger
  cases carrier with
  | inl spinBranch =>
      exact Or.inl
        (And.intro
          (cont_respects_hsame spinBranch.left (hsame_refl ledger)
            endpointLedger (cont_intro rfl))
          spinBranch.right)
  | inr reflectionBranch =>
      exact Or.inr
          (And.intro
          (cont_respects_hsame reflectionBranch.right.left (hsame_refl ledger)
            endpointLedger (cont_intro rfl))
          (And.intro reflectionBranch.left reflectionBranch.right.right))

theorem PinGroupReflectionParityCarrier_reflection_product_closure
    {spin reflection product endpoint product' endpoint' : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      UnaryHistory spin ->
        UnaryHistory reflection ->
          Cont spin reflection product' ->
            hsame endpoint' product' ->
              PinGroupReflectionParityCarrier spin reflection product' endpoint' ∧
                UnaryHistory product' := by
  intro carrier spinUnary reflectionUnary productCont sameEndpoint
  have productUnary : UnaryHistory product' :=
    unary_cont_closed spinUnary reflectionUnary productCont
  cases carrier with
  | inl _spinBranch =>
      exact And.intro
        (Or.inr
          (And.intro productCont
            (And.intro sameEndpoint reflectionUnary)))
        productUnary
  | inr _reflectionBranch =>
      exact And.intro
        (Or.inr
          (And.intro productCont
            (And.intro sameEndpoint reflectionUnary)))
        productUnary

end BEDC.Derived.PinGroupUp
