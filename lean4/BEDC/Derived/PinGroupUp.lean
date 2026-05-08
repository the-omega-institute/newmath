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

end BEDC.Derived.PinGroupUp
