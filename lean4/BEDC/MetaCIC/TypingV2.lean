import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC.V2

/-!
V2 keeps the same term syntax and substitution operation, but changes the
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

/-- V2 typing relation with shift-aware binder context extension. -/
inductive HasTypeV2 : Ctx → Term → Term → Prop
  | sortRule (Γ : Ctx) :
      HasTypeV2 Γ Term.sort Term.sort
  | varRule (Γ : Ctx) (i : Idx) (A : Term) :
      Γ.lookup i = some A →
      HasTypeV2 Γ (Term.var i) A
  | piRule (Γ : Ctx) (dom cod : Term) :
      HasTypeV2 Γ dom Term.sort →
      HasTypeV2 ((shift 0 1 dom) :: Γ) cod Term.sort →
      HasTypeV2 Γ (Term.pi dom cod) Term.sort
  | lamRule (Γ : Ctx) (dom body cod : Term) :
      HasTypeV2 Γ dom Term.sort →
      HasTypeV2 ((shift 0 1 dom) :: Γ) body cod →
      HasTypeV2 Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (Γ : Ctx) (f a dom cod : Term) :
      HasTypeV2 Γ f (Term.pi dom cod) →
      HasTypeV2 Γ a dom →
      HasTypeV2 Γ (Term.app f a) (substitute 0 a cod)

theorem sort_in_empty_ctx : HasTypeV2 [] Term.sort Term.sort :=
  HasTypeV2.sortRule []

theorem dependent_identity_tracks_outer_domain :
    HasTypeV2 [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  apply HasTypeV2.lamRule
  · apply HasTypeV2.varRule
    rfl
  · apply HasTypeV2.varRule
    rfl

theorem substitute_preserves_typing_V2_sort_var
    {Γ : Ctx} {t s A B : Term}
    (hclosed_B : ClosedAt 0 B)
    (ht : HasTypeV2 (B :: Γ) t A)
    (hs : HasTypeV2 Γ s B)
    (hshape : t = Term.sort ∨ ∃ i : Idx, t = Term.var i) :
    HasTypeV2 Γ (substitute 0 s t) (substitute 0 s A) := by
  cases ht with
  | sortRule Δ =>
      exact HasTypeV2.sortRule Γ
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
              exact HasTypeV2.varRule Γ n T hlook
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

def r11SubstitutionTermV2 : Term :=
  Term.lam (Term.var 0) (Term.var 0)

def r11SubstitutionTypeV2 : Term :=
  Term.pi (Term.var 0) (Term.var 1)

def r11CapturedType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

theorem r11_source_typed_V2 :
    HasTypeV2 [Term.sort] r11SubstitutionTermV2 r11SubstitutionTypeV2 := by
  unfold r11SubstitutionTermV2
  unfold r11SubstitutionTypeV2
  exact dependent_identity_tracks_outer_domain

theorem r11_substitution_target_shape_V2 :
    substitute 0 Term.sort r11SubstitutionTermV2 =
        Term.lam Term.sort (Term.var 0) ∧
      substitute 0 Term.sort r11SubstitutionTypeV2 =
        Term.pi Term.sort Term.sort := by
  constructor
  · rfl
  · rfl

theorem r11_substitute_preserves_typing_V2 :
    HasTypeV2 []
      (substitute 0 Term.sort r11SubstitutionTermV2)
      (substitute 0 Term.sort r11SubstitutionTypeV2) := by
  change HasTypeV2 []
    (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort)
  apply HasTypeV2.lamRule
  · exact HasTypeV2.sortRule []
  · apply HasTypeV2.varRule
    rfl

theorem r11_captured_target_rejected_V2 :
    ¬ HasTypeV2 []
      (substitute 0 Term.sort r11SubstitutionTermV2)
      (substitute 0 Term.sort r11CapturedType) := by
  intro h
  change HasTypeV2 []
    (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort (Term.var 0)) at h
  cases h with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup

end BEDC.MetaCIC.V2
