import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.PinGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem PinGroupReflectionParityCarrier_semantic_name_certificate
    {spin reflection product endpoint : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      SemanticNameCert
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun left right : BHist =>
            PinGroupReflectionParityCarrier spin reflection product left ∧
              PinGroupReflectionParityCarrier spin reflection product right ∧ hsame left right) ∧
        (hsame endpoint spin ∨ hsame endpoint product) := by
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun left right : BHist =>
            PinGroupReflectionParityCarrier spin reflection product left ∧
              PinGroupReflectionParityCarrier spin reflection product right ∧ hsame left right) := {
    core := {
      carrier_inhabited := Exists.intro endpoint carrier
      equiv_refl := by
        intro row rowCarrier
        exact And.intro rowCarrier (And.intro rowCarrier (hsame_refl row))
      equiv_symm := by
        intro left right related
        exact And.intro related.right.left
          (And.intro related.left (hsame_symm related.right.right))
      equiv_trans := by
        intro left middle right relatedLM relatedMR
        exact And.intro relatedLM.left
          (And.intro relatedMR.right.left
            (hsame_trans relatedLM.right.right relatedMR.right.right))
      carrier_respects_equiv := by
        intro left right related _leftCarrier
        exact related.right.left
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  constructor
  · exact cert
  · cases carrier with
    | inl spinBranch =>
        exact Or.inl spinBranch.left
    | inr reflectionBranch =>
        exact Or.inr reflectionBranch.right.left

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

theorem PinGroupReflectionParityLedgerSurface_parity_scope_transport
    {spin reflection product endpoint ledger carried spin' reflection' product' endpoint' ledger'
      carried' : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      hsame spin spin' ->
        hsame reflection reflection' ->
          hsame product product' ->
            hsame endpoint endpoint' ->
              hsame ledger ledger' ->
                Cont spin' reflection' product' ->
                  Cont endpoint' ledger' carried' ->
                    PinGroupReflectionParityLedgerSurface spin' reflection' product' endpoint'
                        ledger' carried' ∧
                      hsame carried carried' ∧
                        (((hsame carried' (append spin' ledger') ∧ UnaryHistory spin') ∨
                            (hsame carried' (append product' ledger') ∧
                              Cont spin' reflection' product' ∧ UnaryHistory reflection')) ∧
                          hsame carried' (append endpoint' ledger')) := by
  intro surface sameSpin sameReflection sameProduct sameEndpoint sameLedger productRow'
    endpointLedgerRow'
  have carrier' :
      PinGroupReflectionParityCarrier spin' reflection' product' endpoint' :=
    PinGroupReflectionParityCarrier_stability surface.left sameSpin sameReflection sameProduct
      sameEndpoint productRow'
  have surface' :
      PinGroupReflectionParityLedgerSurface spin' reflection' product' endpoint' ledger' carried' :=
    And.intro carrier' endpointLedgerRow'
  have sameCarried : hsame carried carried' :=
    cont_respects_hsame sameEndpoint sameLedger surface.right endpointLedgerRow'
  exact And.intro surface'
    (And.intro sameCarried (PinGroupReflectionParityLedgerSurface_exhaustion surface'))

theorem PinGroupReflectionParityCarrier_source_projection_no_confusion
    {spin reflection product endpoint : BHist} :
    PinGroupReflectionParityCarrier spin reflection product endpoint ->
      (hsame spin product -> False) ->
        ((hsame endpoint spin ∧ hsame endpoint product) -> False) ∧
          ((Cont spin reflection product ∧ hsame endpoint product) ->
            hsame endpoint spin -> False) := by
  intro carrier spinProductSeparated
  cases carrier with
  | inl _spinBranch =>
      constructor
      · intro simultaneous
        exact spinProductSeparated
          (hsame_trans (hsame_symm simultaneous.left) simultaneous.right)
      · intro productProjection endpointSpin
        exact spinProductSeparated
          (hsame_trans (hsame_symm endpointSpin) productProjection.right)
  | inr _reflectionBranch =>
      constructor
      · intro simultaneous
        exact spinProductSeparated
          (hsame_trans (hsame_symm simultaneous.left) simultaneous.right)
      · intro productProjection endpointSpin
        exact spinProductSeparated
          (hsame_trans (hsame_symm endpointSpin) productProjection.right)

theorem PinGroupReflectionParityCarrier_namecert_obligation_surface
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      SemanticNameCert
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun row : BHist => PinGroupReflectionParityCarrier spin reflection product row)
          (fun left right : BHist =>
            PinGroupReflectionParityCarrier spin reflection product left ∧
              PinGroupReflectionParityCarrier spin reflection product right ∧ hsame left right) ∧
        (((hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
            (hsame carried (append product ledger) ∧ Cont spin reflection product ∧
              UnaryHistory reflection)) ∧
          hsame carried (append endpoint ledger)) ∧
          (hsame endpoint spin ∨ hsame endpoint product) := by
  intro surface
  have certRows := PinGroupReflectionParityCarrier_semantic_name_certificate surface.left
  have ledgerRows := PinGroupReflectionParityLedgerSurface_exhaustion surface
  exact And.intro certRows.left (And.intro ledgerRows certRows.right)

end BEDC.Derived.PinGroupUp
