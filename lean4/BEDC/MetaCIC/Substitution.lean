import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- 目标替换保持命题的完整形状。 -/
def SubstitutePreservesTypingStatement : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    HasType (B :: Γ) t A →
    HasType Γ s B →
    HasType Γ (substitute 0 s t) (substitute 0 s A)

/-- sort 上的替换按定义保持 sort。 -/
theorem substitute_sort (d : Idx) (v : Term) :
    substitute d v Term.sort = Term.sort := by
  rfl

/-- 深度零变量被替换项本身取代。 -/
theorem substitute_var_zero (v : Term) :
    substitute 0 v (Term.var 0) = v := by
  unfold substitute
  rfl

/-- 深度零替换穿过正变量时删除一个 binder 层。 -/
theorem substitute_var_succ_zero (v : Term) (i : Idx) :
    substitute 0 v (Term.var (i + 1)) = Term.var i := by
  cases i
  · unfold substitute
    rfl
  · unfold substitute
    rfl

/-- cons 上第零变量的类型就是栈顶类型。 -/
theorem lookup_cons_zero (Γ : Ctx) (B : Term) :
    Ctx.lookup (B :: Γ) 0 = some B := by
  rfl

/-- cons 下方变量 lookup 会提升返回类型。 -/
theorem lookup_cons_succ (Γ : Ctx) (B : Term) (i : Idx) :
    Ctx.lookup (B :: Γ) (i + 1) =
      match Ctx.lookup Γ i with
      | some T => some (shift 0 1 T)
      | none => none := by
  rfl

/-- 当前规则允许 `var 0 : var 1`。 -/
theorem open_context_var_zero_has_var_one :
    HasType [Term.var 1] (Term.var 0) (Term.var 1) := by
  apply HasType.varRule
  rfl

/-- 在同一上下文中并不能推出 `var 0 : var 0`。 -/
theorem open_context_var_zero_not_has_var_zero :
    ¬ HasType [Term.var 1] (Term.var 0) (Term.var 0) := by
  intro h
  cases h with
  | varRule Γ i A hlookup =>
      unfold Ctx.lookup at hlookup
      cases hlookup

/--
`SubstitutePreservesTypingStatement` 在当前开放上下文规则下为假。

取 `Γ = [var 1]`, `B = var 1`, `s = var 0`, `t = var 0`, `A = var 1`。
两个前提均由 `varRule` 成立，但结论要求 `var 0 : var 0`。
-/
theorem substitute_preserves_typing_statement_false :
    ¬ SubstitutePreservesTypingStatement := by
  intro h
  exact open_context_var_zero_not_has_var_zero
    (h
      (Γ := [Term.var 1])
      (t := Term.var 0)
      (s := Term.var 0)
      (A := Term.var 1)
      (B := Term.var 1)
      (by
        apply HasType.varRule
        rfl)
      open_context_var_zero_has_var_one)

/--
TODO: 主定理仍保留为占位。当前无良构上下文或类型转换规则时，
上面的反例证明目标形状不可证。
-/
theorem substitute_preserves_typing : True := True.intro

end BEDC.MetaCIC
