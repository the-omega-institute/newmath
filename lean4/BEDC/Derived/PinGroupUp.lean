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

theorem PinGroupReflectionParityCarrier_parity_carrier_inversion
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      Cont endpoint ledger carried ->
        ((hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
            (hsame carried (append product ledger) ∧
              Cont spin reflection product ∧ UnaryHistory reflection)) ∧
          (hsame endpoint spin ∨ hsame endpoint product) := by
  intro carrier endpointLedger
  constructor
  · cases carrier with
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
  · cases carrier with
    | inl spinBranch => exact Or.inl spinBranch.left
    | inr reflectionBranch => exact Or.inr reflectionBranch.right.left

def PinGroupReflectionParityLedgerSurface
    (spin reflection product endpoint ledger carried : BHist) : Prop :=
  PinGroupReflectionParityCarrier spin reflection product endpoint ∧ Cont endpoint ledger carried

theorem PinGroupReflectionParityLedgerSurface_exhaustion
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      ((hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
          (hsame carried (append product ledger) ∧ Cont spin reflection product ∧
            UnaryHistory reflection)) ∧
        hsame carried (append endpoint ledger) := by
  intro surface
  have branchExhaustion :=
    PinGroupReflectionParityCarrier_exactness surface.left surface.right
  exact And.intro branchExhaustion surface.right

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

theorem PinGroupReflectionParityCarrier_odd_reflection_coset_exhaustion
    {spin reflection product endpoint : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      (hsame endpoint spin -> False) ->
        Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection := by
  intro carrier notSpinEndpoint
  cases carrier with
  | inl spinBranch =>
      exact False.elim (notSpinEndpoint spinBranch.left)
  | inr reflectionBranch =>
      exact reflectionBranch

theorem PinGroupReflectionParityLedgerSurface_reflection_ledger_closure
    {spin reflection product endpoint ledger carried spin' reflection' product' endpoint'
      carried' : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      hsame spin spin' ->
        hsame reflection reflection' ->
          hsame product product' ->
            hsame endpoint endpoint' ->
              hsame carried carried' ->
                Cont spin' reflection' product' ->
                  Cont endpoint' ledger carried' ->
                    PinGroupReflectionParityLedgerSurface spin' reflection' product' endpoint'
                        ledger carried' ∧
                      (((hsame carried' (append spin' ledger) ∧ UnaryHistory spin') ∨
                            (hsame carried' (append product' ledger) ∧
                              Cont spin' reflection' product' ∧ UnaryHistory reflection')) ∧
                        hsame carried' (append endpoint' ledger)) := by
  intro surface sameSpin sameReflection sameProduct sameEndpoint _sameCarried productRow'
    endpointRow'
  have carrier' :
      PinGroupReflectionParityCarrier spin' reflection' product' endpoint' :=
    PinGroupReflectionParityCarrier_stability surface.left sameSpin sameReflection sameProduct
      sameEndpoint productRow'
  have surface' :
      PinGroupReflectionParityLedgerSurface spin' reflection' product' endpoint' ledger carried' :=
    And.intro carrier' endpointRow'
  exact And.intro surface' (PinGroupReflectionParityLedgerSurface_exhaustion surface')

end BEDC.Derived.PinGroupUp
