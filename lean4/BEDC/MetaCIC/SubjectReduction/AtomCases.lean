import BEDC.MetaCIC.SubjectReduction.Hypotheses

namespace BEDC.MetaCIC

theorem betaSubstitutionPreservation_sort_var
    {Γ : Ctx} {dom body arg cod : Term}
    (hbody : HasType ((shift 0 1 dom) :: Γ) body cod)
    (harg : HasType Γ arg dom)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasType Γ (substitute 0 arg body) (substitute 0 arg cod) := by
  cases hbody with
  | sortRule Δ =>
      exact HasType.sortRule Γ
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
              exact HasType.varRule Γ i T hlook
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

theorem subject_reduction_beta_sort_var
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasType Γ (Term.app (Term.lam dom body) arg) A)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasType Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact betaSubstitutionPreservation_sort_var hbody ha hshape

end BEDC.MetaCIC
