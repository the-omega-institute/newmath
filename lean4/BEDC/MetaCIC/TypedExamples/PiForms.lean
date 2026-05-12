import BEDC.MetaCIC.TypedExamples.Sorts

namespace BEDC.MetaCIC

theorem two_sort_vars :
    HasType [Term.sort, Term.sort] (Term.pi (Term.var 0) (Term.var 1)) Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem lam_pi_var0_var1 :
    HasType [Term.sort]
      (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1)))
      (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule [Term.sort]
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem lam_pi_var_var :
    HasType []
      (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1)))
      (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

/-- 在 [sort] ctx 下: pi (var 0) sort 类型为 sort. -/
theorem pi_var_sort_in_sort_ctx :
    HasType [Term.sort] (Term.pi (Term.var 0) Term.sort) Term.sort := by
  apply HasType.piRule
  · exact var_zero_in_sort_ctx
  · exact HasType.sortRule _

theorem pi_using_arrow_in_ctx :
    HasType [Term.pi Term.sort Term.sort]
      (Term.pi (Term.app (Term.var 0) Term.sort) Term.sort)
      Term.sort := by
  apply HasType.piRule
  · exact HasType.appRule [Term.pi Term.sort Term.sort]
      (Term.var 0)
      Term.sort
      Term.sort
      Term.sort
      (HasType.varRule [Term.pi Term.sort Term.sort] 0
        (Term.pi Term.sort Term.sort) rfl)
      (HasType.sortRule [Term.pi Term.sort Term.sort])
  · exact HasType.sortRule _

/-- 在 [sort] ctx 下: lam (var 0) (var 0) 类型为 pi (var 0) (var 1). 这是 dependent identity. -/

theorem pi_sort_sort_in_empty_ctx :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  exact pi_sort_sort_well_typed

theorem pi_sort_dependent :
    HasType [Term.sort] (Term.pi Term.sort (Term.var 1)) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule [Term.sort]
  · apply HasType.varRule
    rfl

theorem nested_pi_sort_sort :
    HasType [] (Term.pi Term.sort (Term.pi Term.sort Term.sort)) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · exact HasType.sortRule [Term.sort, Term.sort]

theorem triple_pi_sort :
    HasType []
      (Term.pi Term.sort (Term.pi Term.sort (Term.pi Term.sort Term.sort)))
      Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · exact HasType.sortRule [Term.sort, Term.sort]
      · exact HasType.sortRule [Term.sort, Term.sort, Term.sort]

/-- 空 ctx 下: pi sort (pi (var 0) (var 1)) 类型为 sort. -/
theorem nested_pi_dep_in_empty :
    HasType [] (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))) Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl


theorem nested_pi_var_sort :
    HasType [Term.sort] (Term.pi (Term.var 0) (Term.pi (Term.var 1) Term.sort))
      Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · exact HasType.sortRule [Term.var 2, Term.var 1, Term.sort]

/-- 单 sort ctx 下: lambda 构造把外层 type 映到 pi (var 1) sort 的 type 操作. -/
theorem map_pi_in_sort_ctx :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.pi (Term.var 1) Term.sort))
      (Term.pi (Term.var 0) Term.sort) := by
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · exact HasType.sortRule [Term.var 2, Term.var 1, Term.sort]

/-- 空 ctx 下: app (lam sort (var 0)) sort 类型为 sort. -/

theorem triple_lam_pi_construction :
    HasType []
      (Term.lam Term.sort
        (Term.lam Term.sort
          (Term.lam (Term.var 1)
            (Term.pi (Term.var 1) (Term.var 2)))))
      (Term.pi Term.sort
        (Term.pi Term.sort
          (Term.pi (Term.var 1) Term.sort))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.piRule
        · apply HasType.varRule
          rfl
        · apply HasType.varRule
          rfl


theorem double_poly_pi :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort (Term.pi (Term.var 1) (Term.var 1))))
      (Term.pi Term.sort (Term.pi Term.sort Term.sort)) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.piRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl

theorem double_arrow_in_sort :
    HasType [Term.sort]
      (Term.pi (Term.var 0) (Term.pi (Term.var 1) (Term.var 2)))
      Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem pi_var_var_in_quad_sort :
    HasType [Term.sort, Term.sort, Term.sort, Term.sort]
      (Term.pi (Term.var 0) (Term.var 1))
      Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

theorem nested_pi_chain :
    HasType []
      (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1)))
      Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl


theorem pi_function_to_sort_in_empty :
    HasType []
      (Term.pi (Term.pi Term.sort Term.sort) Term.sort)
      Term.sort := by
  apply HasType.piRule
  · exact pi_sort_sort_in_empty_ctx
  · exact HasType.sortRule [Term.pi Term.sort Term.sort]


theorem function_of_function :
    HasType []
      (Term.pi (Term.pi Term.sort Term.sort) (Term.pi (Term.pi Term.sort Term.sort) Term.sort))
      Term.sort := by
  apply HasType.piRule
  · exact pi_sort_sort_in_empty_ctx
  · apply HasType.piRule
    · apply HasType.piRule
      · exact HasType.sortRule [Term.pi Term.sort Term.sort]
      · exact HasType.sortRule [Term.sort, Term.pi Term.sort Term.sort]
    · exact HasType.sortRule [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]

theorem nested_shifted_pi_in_sort :
    HasType [Term.sort]
      (Term.pi (Term.var 0) (Term.pi (Term.var 1) (Term.var 2)))
      Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl


end BEDC.MetaCIC
