import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.TypingV2

namespace BEDC.MetaCIC.V2

def BetaSubstitutionPreservationV2 : Prop :=
  ∀ {Γ : Ctx} {dom body arg cod : Term},
    HasTypeV2 ((shift 0 1 dom) :: Γ) body cod →
    HasTypeV2 Γ arg dom →
    HasTypeV2 Γ (substitute 0 arg body) (substitute 0 arg cod)

theorem betaSubstitutionPreservationV2_sort_var
    {Γ : Ctx} {dom body arg cod : Term}
    (hbody : HasTypeV2 ((shift 0 1 dom) :: Γ) body cod)
    (harg : HasTypeV2 Γ arg dom)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasTypeV2 Γ (substitute 0 arg body) (substitute 0 arg cod) := by
  cases hbody with
  | sortRule Δ =>
      exact HasTypeV2.sortRule Γ
  | varRule Δ i _ hlookup =>
      cases i with
      | zero =>
          change some (shift 0 1 dom) = some cod at hlookup
          cases hlookup
          rw [substitute_var_zero]
          rw [substitute_shift_at_eq]
          exact harg
      | succ i =>
          rw [lookup_cons_succ] at hlookup
          cases hlook : Ctx.lookup Γ i with
          | none =>
              rw [hlook] at hlookup
              cases hlookup
          | some T =>
              rw [hlook] at hlookup
              cases hlookup
              rw [substitute_var_succ_zero]
              rw [substitute_shift_at_eq]
              exact HasTypeV2.varRule Γ i T hlook
  | piRule Δ piDom piCod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ lamDom lamBody lamCod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a appDom appCod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

theorem subject_reduction_V2_beta_sort_var
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasTypeV2 Γ (Term.app (Term.lam dom body) arg) A)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasTypeV2 Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact betaSubstitutionPreservationV2_sort_var hbody ha hshape

theorem subject_reduction_V2_beta
    (hsubst : BetaSubstitutionPreservationV2)
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasTypeV2 Γ (Term.app (Term.lam dom body) arg) A) :
    HasTypeV2 Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact hsubst hbody ha

end BEDC.MetaCIC.V2
