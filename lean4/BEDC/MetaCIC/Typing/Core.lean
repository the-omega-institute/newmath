import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

/-!
 keeps the same term syntax and substitution operation, but changes the
context extension used by binders.  When a domain type is checked in `Γ`, its
free variables are relative to `Γ`; under a new binder, the same outside
variables must be shifted by one.  Therefore the binder slot stores
`shift 0 1 dom`, not `dom`.

For the stress term `lam (var 0) (var 0)` in context `[sort]`, the body
variable has type `var 1` under the binder.  The resulting Pi type is
`pi (var 0) (var 1)`, so the outside variable is not captured by the Pi binder.
This is the local substrate change needed before preservation statements can be
restated against the same de Bruijn syntax.
-/

/--  typing relation with shift-aware binder context extension. -/
inductive HasType : Ctx → Term → Term → Prop
  | sortRule (Γ : Ctx) :
      HasType Γ Term.sort Term.sort
  | varRule (Γ : Ctx) (i : Idx) (A : Term) :
      Γ.lookup i = some A →
      HasType Γ (Term.var i) A
  | piRule (Γ : Ctx) (dom cod : Term) :
      HasType Γ dom Term.sort →
      HasType ((shift 0 1 dom) :: Γ) cod Term.sort →
      HasType Γ (Term.pi dom cod) Term.sort
  | lamRule (Γ : Ctx) (dom body cod : Term) :
      HasType Γ dom Term.sort →
      HasType ((shift 0 1 dom) :: Γ) body cod →
      HasType Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (Γ : Ctx) (f a dom cod : Term) :
      HasType Γ f (Term.pi dom cod) →
      HasType Γ a dom →
      HasType Γ (Term.app f a) (substitute 0 a cod)

theorem sort_in_empty_ctx : HasType [] Term.sort Term.sort :=
  HasType.sortRule []

theorem dependent_identity_tracks_outer_domain :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem id_sort_well_typed :
    HasType [] (Term.lam Term.sort (Term.var 0))
      (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem pi_sort_sort_well_typed :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact HasType.sortRule [Term.sort]

theorem id_sort_applied :
    HasType []
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort := by
  exact HasType.appRule
    []
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    Term.sort
    Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

theorem pi_dependent_identity_type :
    HasType [Term.sort] (Term.pi (Term.var 0) (Term.var 1)) Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem dependent_id_differs_from_V6 :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_identity_tracks_outer_domain

theorem substitute_sort_preserves
    {Γ : Ctx} {s : Term} :
    HasType Γ (substitute 0 s Term.sort) (substitute 0 s Term.sort) := by
  exact HasType.sortRule Γ

theorem substitute_var_zero_preserves_typing_closed
    {Γ : Ctx} {s B : Term}
    (hclosed_B : ClosedAt 0 B)
    (hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.var 0))
      (substitute 0 s B) := by
  rw [substitute_var_zero]
  rw [substitute_closed_via_term_induction 0 s B hclosed_B]
  exact hs

theorem substitute_var_succ_preserves_typing
    {Γ : Ctx} {s A : Term} {i : Idx}
    (hlook : Ctx.lookup Γ i = some A) :
    HasType Γ
      (substitute 0 s (Term.var (i + 1)))
      (substitute 0 s (shift 0 1 A)) := by
  rw [substitute_var_succ_zero]
  rw [substitute_shift_at_eq]
  exact HasType.varRule Γ i A hlook

theorem substitute_preserves_typing_sort_var
    {Γ : Ctx} {t s A B : Term}
    (hclosed_B : ClosedAt 0 B)
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  cases ht with
  | sortRule Δ =>
      exact HasType.sortRule Γ
  | varRule Δ i A hlookup =>
      cases i with
      | zero =>
          change some B = some A at hlookup
          cases hlookup
          rw [substitute_var_zero]
          rw [substitute_closed 0 s A hclosed_B]
          exact hs
      | succ n =>
          rw [substitute_var_succ_zero]
          rw [lookup_cons_succ] at hlookup
          cases hlook : Ctx.lookup Γ n with
          | none =>
              rw [hlook] at hlookup
              cases hlookup
          | some T =>
              rw [hlook] at hlookup
              cases hlookup
              rw [substitute_shift_at_eq]
              exact HasType.varRule Γ n T hlook
  | piRule Δ dom cod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ dom body cod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a dom cod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

theorem substitute_preserves_typing_binder_head_shape
    {s dom : Term}
    (hclosed_s : ClosedAt 0 s) :
    substitute 1 (shift 0 1 s) (shift 0 1 dom) =
      shift 0 1 (substitute 0 s dom) := by
  rw [← shift_substitute_zero_zero_closed s dom hclosed_s]

theorem substitute_preserves_typing_pi_if_subderivations
    {Γ : Ctx} {s B dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasType Γ (substitute 0 s dom) Term.sort)
    (hcod_sub :
      HasType ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) cod)
        Term.sort)
    (_hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.pi dom cod))
      (substitute 0 s Term.sort) := by
  change HasType Γ
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
    Term.sort
  apply HasType.piRule
  · exact hdom_sub
  · exact hcod_sub

theorem substitute_preserves_typing_lam_if_subderivations
    {Γ : Ctx} {s B dom body cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hdom_sub : HasType Γ (substitute 0 s dom) Term.sort)
    (hbody_sub :
      HasType ((shift 0 1 (substitute 0 s dom)) :: Γ)
        (substitute 1 (shift 0 1 s) body)
        (substitute 1 (shift 0 1 s) cod))
    (_hs : HasType Γ s B) :
    HasType Γ
      (substitute 0 s (Term.lam dom body))
      (substitute 0 s (Term.pi dom cod)) := by
  change HasType Γ
    (Term.lam (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) body))
    (Term.pi (substitute 0 s dom)
      (substitute 1 (shift 0 1 s) cod))
  apply HasType.lamRule
  · exact hdom_sub
  · exact hbody_sub

theorem substitute_preserves_typing_app_if_subderivations
    {Γ : Ctx} {s B f a dom cod : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hf_sub :
      HasType Γ
        (substitute 0 s f)
        (Term.pi (substitute 0 s dom)
          (substitute 1 (shift 0 1 s) cod)))
    (ha_sub :
      HasType Γ
        (substitute 0 s a)
        (substitute 0 s dom))
    (_hs : HasType Γ s B)
    (hcod_sub :
      substitute 0 (substitute 0 s a)
        (substitute 1 (shift 0 1 s) cod) =
      substitute 0 s (substitute 0 a cod)) :
    HasType Γ
      (substitute 0 s (Term.app f a))
      (substitute 0 s (substitute 0 a cod)) := by
  change HasType Γ
    (Term.app (substitute 0 s f) (substitute 0 s a))
    (substitute 0 s (substitute 0 a cod))
  rw [← hcod_sub]
  apply HasType.appRule
  · exact hf_sub
  · exact ha_sub


end BEDC.MetaCIC
