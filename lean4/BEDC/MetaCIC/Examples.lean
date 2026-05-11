import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Substitution
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

/-- 在 Sort 宇宙下, 类型上的恒等函数 `λ (T : Sort). T`。 -/
def id_sort : Term := Term.lam Term.sort (Term.var 0)

theorem id_sort_well_typed :
    HasType [] id_sort (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem pi_sort_sort_well_typed :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact HasType.sortRule [Term.sort]

/-- `Sort` 在空上下文边界处闭合。 -/
theorem sort_closed_at_zero : ClosedAt 0 Term.sort :=
  ClosedAt.sortClosed

/-- `Sort` 在一变量边界处也闭合。 -/
theorem sort_closed_at_one : ClosedAt 1 Term.sort :=
  ClosedAt.sortClosed

/-- `Π (_ : Sort), Sort` 在空上下文边界处闭合。 -/
theorem pi_sort_sort_closed : ClosedAt 0 (Term.pi Term.sort Term.sort) := by
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · exact ClosedAt.sortClosed

/-- `id_sort` 应用到 `Term.sort` 上。 -/
theorem id_sort_applied :
    HasType [] (Term.app id_sort Term.sort) Term.sort := by
  exact HasType.appRule
    []
    id_sort
    Term.sort
    Term.sort
    Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

/-- `(λ (T : Sort). T) Sort →β Sort`。 -/
theorem id_sort_beta :
    BetaStep (Term.app id_sort Term.sort) Term.sort := by
  exact BetaStep.beta Term.sort (Term.var 0) Term.sort

/-- 在 `[Term.sort]` 上下文里, `var 0` 类型是 `Term.sort`。 -/
theorem var_zero_in_sort_ctx :
    HasType [Term.sort] (Term.var 0) Term.sort := by
  apply HasType.varRule
  rfl

/-- K 组合子: `λ (x : Sort). λ (_ : Sort). x`。 -/
def kCombinator : Term :=
  Term.lam Term.sort (Term.lam Term.sort (Term.var 1))

def kCombinatorType : Term :=
  Term.pi Term.sort (Term.pi Term.sort Term.sort)

theorem k_combinator_well_typed :
    HasType [] kCombinator kCombinatorType := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.varRule
      rfl

/-- `K Sort Sort` 的类型回到 `Sort`。 -/
theorem k_applied_twice :
    HasType [] (Term.app (Term.app kCombinator Term.sort) Term.sort) Term.sort := by
  have hFirst :
      HasType [] (Term.app kCombinator Term.sort) (Term.pi Term.sort Term.sort) := by
    exact HasType.appRule
      []
      kCombinator
      Term.sort
      Term.sort
      (Term.pi Term.sort Term.sort)
      k_combinator_well_typed
      (HasType.sortRule [])
  exact HasType.appRule
    []
    (Term.app kCombinator Term.sort)
    Term.sort
    Term.sort
    Term.sort
    hFirst
    (HasType.sortRule [])

/-- `K` 组合子本身是闭合项。 -/
theorem k_combinator_closed : ClosedAt 0 kCombinator := by
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.varClosed
      exact Nat.lt_add_one 1

/-- `λ (f : Sort → Sort). λ (x : Sort). x` 的 Sort-level zero-like term。 -/
def churchZeroSort : Term :=
  Term.lam (Term.pi Term.sort Term.sort) (Term.lam Term.sort (Term.var 0))

def churchZeroSortType : Term :=
  Term.pi (Term.pi Term.sort Term.sort) (Term.pi Term.sort Term.sort)

theorem church_zero_sort_well_typed :
    HasType [] churchZeroSort churchZeroSortType := by
  apply HasType.lamRule
  · apply HasType.piRule
    · exact HasType.sortRule []
    · exact HasType.sortRule [Term.sort]
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.pi Term.sort Term.sort]
    · apply HasType.varRule
      rfl

/-- 在 Sort 原子项上, 同深度替换抵消一层同深度提升。 -/
theorem sort_shift_substitute_identity :
    substitute 0 Term.sort (shift 0 1 Term.sort) = Term.sort := by
  exact substitute_shift_at_eq 0 Term.sort Term.sort

/-- 具体闭合替换路线中, 替换项和被替换目标都满足闭合前提。 -/
theorem concrete_closed_subst_preconditions :
    ClosedAt 0 Term.sort ∧ ClosedAt 0 Term.sort ∧
      substitute 0 Term.sort Term.sort = Term.sort := by
  refine ⟨?_, ?_, ?_⟩
  · exact ClosedAt.sortClosed
  · exact ClosedAt.sortClosed
  · exact substitute_closed 0 Term.sort Term.sort ClosedAt.sortClosed

/-- 一个具体闭合项替换后的 typing 结论。 -/
theorem concrete_closed_subst_preserves :
    let Γ : Ctx := []
    let B : Term := Term.sort
    let s : Term := Term.sort
    let t : Term := Term.sort
    let A : Term := Term.sort
    ClosedAt 0 B ∧ HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  refine ⟨?_, ?_⟩
  · exact ClosedAt.sortClosed
  · exact HasType.sortRule []

/-- 深度一替换在目标变量上命中替换项。 -/
theorem substitute_at_one_var_one (v : Term) :
    substitute 1 v (Term.var 1) = v := by
  unfold substitute
  rfl

/-- 深度一替换穿过更高变量时删除一层 binder。 -/
theorem substitute_at_one_var_two (v : Term) :
    substitute 1 v (Term.var 2) = Term.var 1 := by
  unfold substitute
  rfl

/-- `lam` 下 descend 后, depth-1 替换命中 body 中对应的外层引用。 -/
theorem concrete_depth_one_lam_example :
    substitute 1 Term.sort (Term.lam Term.sort (Term.var 2)) =
      Term.lam Term.sort Term.sort := by
  unfold substitute
  unfold shift
  rfl

/-- β-step 的目标项可由 V6 替换-提升抵消引理回到 Sort。 -/
theorem beta_shifted_sort_step_preserves_sort_typing :
    BetaStep (Term.app (Term.lam Term.sort (shift 0 1 Term.sort)) Term.sort) Term.sort ∧
    HasType [] (Term.app (Term.lam Term.sort (shift 0 1 Term.sort)) Term.sort) Term.sort ∧
    HasType [] Term.sort Term.sort := by
  have hSub : substitute 0 Term.sort (shift 0 1 Term.sort) = Term.sort := by
    exact substitute_shift_at_eq 0 Term.sort Term.sort
  refine ⟨?_, ?_, ?_⟩
  · rw [← hSub]
    exact BetaStep.beta Term.sort (shift 0 1 Term.sort) Term.sort
  · exact HasType.appRule
      []
      (Term.lam Term.sort (shift 0 1 Term.sort))
      Term.sort
      Term.sort
      Term.sort
      (HasType.lamRule
        []
        Term.sort
        (shift 0 1 Term.sort)
        Term.sort
        (HasType.sortRule [])
        (HasType.sortRule [Term.sort]))
      (HasType.sortRule [])
  · exact HasType.sortRule []

/-- 嵌套 Pi 项上, V6 替换-提升抵消引理穿过 binder 后仍保持结构。 -/
theorem nested_pi_shift_substitute_identity :
    substitute 0 Term.sort
        (shift 0 1 (Term.pi Term.sort (Term.pi Term.sort Term.sort))) =
      Term.pi Term.sort (Term.pi Term.sort Term.sort) := by
  exact substitute_shift_at_eq 0 Term.sort
    (Term.pi Term.sort (Term.pi Term.sort Term.sort))

end BEDC.MetaCIC
