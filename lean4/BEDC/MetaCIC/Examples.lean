import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Beta

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

end BEDC.MetaCIC
