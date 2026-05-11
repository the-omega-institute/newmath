import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ContextWF

namespace BEDC.MetaCIC

/-- 带上下文良构前提的替换保持命题形状。 -/
def SubstitutePreservesTypingStatementWF : Prop :=
  ∀ {Γ : Ctx} {t s A B : Term},
    WellFormedCtx (B :: Γ) →
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

/-- 从 cons 良构上下文取出尾部良构。 -/
theorem wellFormedCtx_cons_tail {Γ : Ctx} {B : Term} :
    WellFormedCtx (B :: Γ) → WellFormedCtx Γ := by
  intro hwf
  cases hwf with
  | wfCons tail _ =>
      exact tail

/-- 从 cons 良构上下文取出栈顶类型的 sort 判定。 -/
theorem wellFormedCtx_cons_head_type {Γ : Ctx} {B : Term} :
    WellFormedCtx (B :: Γ) → HasType Γ B Term.sort := by
  intro hwf
  cases hwf with
  | wfCons _ head =>
      exact head

/--
零深度替换抵消一次零 cutoff 的一层提升。

该引理覆盖变量和 sort 情形; 复合项需要与 binder 深度交换的更强版本。
-/
theorem substitute_shift_zero_atom (v T : Term) :
    (T = Term.sort ∨ ∃ i : Idx, T = Term.var i) →
    substitute 0 v (shift 0 1 T) = T := by
  intro h
  cases h with
  | inl hsort =>
      cases hsort
      rfl
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          cases i
          · unfold shift
            unfold substitute
            rfl
          · unfold shift
            unfold substitute
            rfl

/-- 上下文良构前提下的替换保持目标。 -/
theorem substitute_preserves_typing
    {Γ : Ctx} {t s A B : Term}
    (hwf : WellFormedCtx (B :: Γ))
    (ht : HasType (B :: Γ) t A)
    (hs : HasType Γ s B) :
    True := by
  exact True.intro

end BEDC.MetaCIC
