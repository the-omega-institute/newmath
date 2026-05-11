import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

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

end BEDC.MetaCIC.V2
