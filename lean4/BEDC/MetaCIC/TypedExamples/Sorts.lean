import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC


/-- 单 sort ctx 中, var 0 类型为 sort。 -/
theorem var_zero_in_sort_ctx :
    HasType [Term.sort] (Term.var 0) Term.sort := by
  apply HasType.varRule
  rfl

/-- 双 sort ctx 中, var 1 类型为 shift 0 1 sort = sort。 -/
theorem var_one_in_double_sort_ctx :
    HasType [Term.sort, Term.sort] (Term.var 1) Term.sort := by
  apply HasType.varRule
  rfl

/-- 三 sort ctx 中, var 1 指向中间的 sort, 其类型为 sort。 -/
theorem middle_var_in_triple_sort :
    HasType [Term.sort, Term.sort, Term.sort] (Term.var 1) Term.sort := by
  apply HasType.varRule
  rfl

theorem deep_var_in_quad_sort :
    HasType [Term.sort, Term.sort, Term.sort, Term.sort] (Term.var 3) Term.sort := by
  apply HasType.varRule
  rfl

theorem mixed_ctx_vars :
    HasType [Term.sort, Term.pi Term.sort Term.sort] (Term.var 0) Term.sort := by
  apply HasType.varRule
  rfl

theorem mixed_ctx_var_zero :
    HasType [Term.sort, Term.pi Term.sort Term.sort, Term.sort] (Term.var 0) Term.sort := by
  apply HasType.varRule
  rfl

theorem mixed_var_in_three_ctx :
    HasType [Term.pi Term.sort Term.sort, Term.sort, Term.sort]
      (Term.var 1) Term.sort := by
  apply HasType.varRule
  rfl


theorem var_in_quint_sort :
    HasType [Term.sort, Term.sort, Term.sort, Term.sort, Term.sort] (Term.var 4) Term.sort := by
  apply HasType.varRule
  rfl


end BEDC.MetaCIC
