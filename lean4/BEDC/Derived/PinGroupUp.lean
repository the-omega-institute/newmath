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

theorem PinGroupReflectionParityCarrier_source_exhaustion
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      ((hsame endpoint spin ∧ UnaryHistory spin) ∨
          (Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection)) ∧
        hsame carried (append endpoint ledger) := by
  intro surface
  constructor
  · cases surface.left with
    | inl spinBranch =>
        exact Or.inl (And.intro spinBranch.left spinBranch.right)
    | inr reflectionBranch =>
        exact Or.inr
          (And.intro reflectionBranch.left
            (And.intro reflectionBranch.right.left reflectionBranch.right.right))
  · exact surface.right

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

theorem PinGroupReflectionParityLedgerSurface_source_ledger_coverage
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      ((hsame endpoint spin ∧ hsame carried (append spin ledger) ∧ UnaryHistory spin) ∨
          (Cont spin reflection product ∧ hsame endpoint product ∧
            hsame carried (append product ledger) ∧ UnaryHistory reflection)) ∧
        hsame carried (append endpoint ledger) := by
  intro surface
  constructor
  · cases surface.left with
    | inl spinBranch =>
        exact Or.inl
          (And.intro spinBranch.left
            (And.intro
              (cont_respects_hsame spinBranch.left (hsame_refl ledger) surface.right
                (cont_intro rfl))
              spinBranch.right))
    | inr reflectionBranch =>
        exact Or.inr
          (And.intro reflectionBranch.left
            (And.intro reflectionBranch.right.left
              (And.intro
                (cont_respects_hsame reflectionBranch.right.left (hsame_refl ledger)
                  surface.right (cont_intro rfl))
                reflectionBranch.right.right)))
  · exact surface.right

theorem PinGroupReflectionParityCarrier_spin_clifford_source_scope
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      ((hsame endpoint spin ∧ UnaryHistory spin) ∨
          (Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection)) ∧
        hsame carried (append endpoint ledger) := by
  intro surface
  constructor
  · cases surface.left with
    | inl spinBranch =>
        exact Or.inl (And.intro spinBranch.left spinBranch.right)
    | inr reflectionBranch =>
        exact Or.inr
          (And.intro reflectionBranch.left
            (And.intro reflectionBranch.right.left reflectionBranch.right.right))
  · exact surface.right

theorem PinGroupReflectionParityLedgerSurface_spin_boundary_exhaustion
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      UnaryHistory spin -> hsame endpoint spin ->
        hsame carried (append spin ledger) ∧ hsame carried (append endpoint ledger) := by
  intro surface spinUnary sameEndpointSpin
  have spinCarrier : PinGroupReflectionParityCarrier spin reflection product endpoint :=
    Or.inl (And.intro sameEndpointSpin spinUnary)
  have spinExact := PinGroupReflectionParityCarrier_exactness spinCarrier surface.right
  have spinCarried : hsame carried (append spin ledger) :=
    by
      cases spinExact with
      | inl spinBranch =>
          exact spinBranch.left
      | inr _reflectionBranch =>
          exact cont_respects_hsame sameEndpointSpin (hsame_refl ledger) surface.right
            (cont_intro rfl)
  have endpointCarried : hsame carried (append endpoint ledger) :=
    PinGroupReflectionParityLedgerSurface_exhaustion surface |>.right
  exact And.intro spinCarried endpointCarried

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

theorem PinGroupReflectionParityLedgerSurface_reflection_generator_obligation
    {spin reflection product endpoint ledger carried : BHist} :
    UnaryHistory spin ->
      UnaryHistory reflection ->
        Cont spin reflection product ->
          hsame endpoint product ->
            Cont endpoint ledger carried ->
              PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ∧
                UnaryHistory product ∧ hsame carried (append product ledger) := by
  intro spinUnary reflectionUnary productCont sameEndpoint endpointLedger
  have productUnary : UnaryHistory product :=
    unary_cont_closed spinUnary reflectionUnary productCont
  have surface :
      PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried :=
    And.intro
      (Or.inr (And.intro productCont (And.intro sameEndpoint reflectionUnary)))
      endpointLedger
  have carriedProduct : hsame carried (append product ledger) :=
    cont_respects_hsame sameEndpoint (hsame_refl ledger) endpointLedger (cont_intro rfl)
  exact And.intro surface (And.intro productUnary carriedProduct)

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

theorem PinGroupReflectionParityLedgerSurface_reflection_generator_transport_closure
    {spin reflection product endpoint ledger carried reflected : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      Cont reflection carried reflected ->
        ((hsame endpoint spin ∧ UnaryHistory spin) ∨
            (Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection)) ∧
          hsame carried (append endpoint ledger) ∧ hsame reflected (append reflection carried) := by
  intro surface reflectedRow
  exact And.intro surface.left (And.intro surface.right reflectedRow)

theorem PinGroupReflectionParityLedgerSurface_reflection_parity_determinacy
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      (hsame spin product -> False) ->
        ((hsame endpoint spin ∧ hsame endpoint product) -> False) ∧
          ((((hsame carried (append spin ledger) ∧ UnaryHistory spin) ∧
              (hsame carried (append product ledger) ∧ Cont spin reflection product ∧
                UnaryHistory reflection))) -> False) := by
  intro surface spinProductSeparated
  have noConfusion :=
    PinGroupReflectionParityCarrier_source_projection_no_confusion surface.left
      spinProductSeparated
  constructor
  · exact noConfusion.left
  · intro bothBranches
    have sameAppends : hsame (append spin ledger) (append product ledger) :=
      hsame_trans (hsame_symm bothBranches.left.left) bothBranches.right.left
    exact spinProductSeparated (append_right_cancel (k := ledger) sameAppends)

theorem PinGroupReflectionParityCarrier_reflection_generator_obligation
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      (hsame endpoint spin -> False) ->
        Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection ∧
          hsame carried (append product ledger) ∧ hsame carried (append endpoint ledger) := by
  intro surface notSpinEndpoint
  have reflectionBranch :=
    PinGroupReflectionParityCarrier_odd_reflection_coset_exhaustion surface.left notSpinEndpoint
  have surfaceRows :=
    PinGroupReflectionParityLedgerSurface_exhaustion surface
  have carriedProduct : hsame carried (append product ledger) := by
    cases surfaceRows.left with
    | inl spinBranch =>
        have sameAppends : hsame (append endpoint ledger) (append spin ledger) :=
          hsame_trans (hsame_symm surfaceRows.right) spinBranch.left
        have endpointSpin : hsame endpoint spin :=
          append_right_cancel (k := ledger) sameAppends
        exact False.elim (notSpinEndpoint endpointSpin)
    | inr productBranch =>
        exact productBranch.left
  exact And.intro reflectionBranch.left
    (And.intro reflectionBranch.right.left
      (And.intro reflectionBranch.right.right
        (And.intro carriedProduct surfaceRows.right)))

theorem PinGroupReflectionParityCarrier_root_reflection_threshold_exactness
    {spin reflection product endpoint ledger carried : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      (hsame endpoint spin -> False) ->
        PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ∧
          Cont spin reflection product ∧ hsame endpoint product ∧ UnaryHistory reflection ∧
            hsame carried (append product ledger) ∧ hsame carried (append endpoint ledger) := by
  intro surface notSpinEndpoint
  have reflectionRows :=
    PinGroupReflectionParityCarrier_reflection_generator_obligation surface notSpinEndpoint
  exact And.intro surface
      (And.intro reflectionRows.left
        (And.intro reflectionRows.right.left
          (And.intro reflectionRows.right.right.left
            (And.intro reflectionRows.right.right.right.left
              reflectionRows.right.right.right.right))))

theorem PinGroupReflectionGenerator_transport_closure
    {spin reflection product endpoint ledger carried spin' reflection' product' endpoint' ledger'
      carried' : BHist} :
    PinGroupReflectionParityLedgerSurface spin reflection product endpoint ledger carried ->
      (hsame endpoint spin -> False) ->
        hsame spin spin' ->
          hsame reflection reflection' ->
            hsame product product' ->
              hsame endpoint endpoint' ->
                hsame ledger ledger' ->
                  Cont spin' reflection' product' ->
                    Cont endpoint' ledger' carried' ->
                      PinGroupReflectionParityLedgerSurface spin' reflection' product' endpoint'
                          ledger' carried' ∧
                        Cont spin' reflection' product' ∧
                          hsame endpoint' product' ∧
                            UnaryHistory reflection' ∧
                              hsame carried' (append product' ledger') ∧
                                hsame carried' (append endpoint' ledger') := by
  intro surface notSpinEndpoint sameSpin sameReflection sameProduct sameEndpoint sameLedger
    productRow' endpointLedgerRow'
  have transported :=
    PinGroupReflectionParityLedgerSurface_parity_scope_transport surface sameSpin sameReflection
      sameProduct sameEndpoint sameLedger productRow' endpointLedgerRow'
  have notSpinEndpoint' : hsame endpoint' spin' -> False := by
    intro endpointSpin'
    exact notSpinEndpoint
      (hsame_trans sameEndpoint
        (hsame_trans endpointSpin' (hsame_symm sameSpin)))
  have reflected :=
    PinGroupReflectionParityCarrier_reflection_generator_obligation transported.left
      notSpinEndpoint'
  exact And.intro transported.left
    (And.intro reflected.left
      (And.intro reflected.right.left
        (And.intro reflected.right.right.left
          (And.intro reflected.right.right.right.left reflected.right.right.right.right))))

theorem PinGroupReflectionParityCarrier_spin_extension_obligation
    {spin ledger carried : BHist} :
    UnaryHistory spin ->
      Cont spin ledger carried ->
        PinGroupReflectionParityLedgerSurface spin BHist.Empty BHist.Empty spin ledger carried ∧
          hsame carried (append spin ledger) := by
  intro spinUnary spinLedger
  exact And.intro
    (And.intro (Or.inl (And.intro (hsame_refl spin) spinUnary)) spinLedger)
    spinLedger

end BEDC.Derived.PinGroupUp
