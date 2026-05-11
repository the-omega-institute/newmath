import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

/-- Typing context = 类型栈。 -/
abbrev Ctx := List Term

/-- 在 ctx 里 lookup 第 i 个变量的类型；越界返回 none。 -/
def Ctx.lookup : Ctx → Idx → Option Term
  | [], _ => none
  | (t :: _), 0 => some t
  | (_ :: rest), n + 1 => Ctx.lookup rest n

/-- HasType Γ t A: 在 ctx Γ 下，term t 的类型是 A。 -/
inductive HasType : Ctx → Term → Term → Prop
  | sortRule (Γ : Ctx) :
      HasType Γ Term.sort Term.sort
  | varRule (Γ : Ctx) (i : Idx) (A : Term) :
      Γ.lookup i = some A →
      HasType Γ (Term.var i) A
  | piRule (Γ : Ctx) (dom cod : Term) :
      HasType Γ dom Term.sort →
      HasType (dom :: Γ) cod Term.sort →
      HasType Γ (Term.pi dom cod) Term.sort
  | lamRule (Γ : Ctx) (dom body cod : Term) :
      HasType Γ dom Term.sort →
      HasType (dom :: Γ) body cod →
      HasType Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (Γ : Ctx) (f a dom cod : Term) :
      HasType Γ f (Term.pi dom cod) →
      HasType Γ a dom →
      HasType Γ (Term.app f a) cod

theorem sort_in_empty_ctx : HasType [] Term.sort Term.sort :=
  HasType.sortRule []

end BEDC.MetaCIC
