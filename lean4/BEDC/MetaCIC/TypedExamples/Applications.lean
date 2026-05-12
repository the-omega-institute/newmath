import BEDC.MetaCIC.TypedExamples.BasicApplications

namespace BEDC.MetaCIC

theorem app_pi_deep_var :
    HasType [Term.sort, Term.sort, Term.sort, Term.pi Term.sort Term.sort]
      (Term.app (Term.var 3) Term.sort)
      Term.sort := by
  exact HasType.appRule [Term.sort, Term.sort, Term.sort, Term.pi Term.sort Term.sort]
    (Term.var 3)
    Term.sort
    Term.sort
    Term.sort
    (HasType.varRule [Term.sort, Term.sort, Term.sort, Term.pi Term.sort Term.sort] 3
      (Term.pi Term.sort Term.sort) rfl)
    (HasType.sortRule [Term.sort, Term.sort, Term.sort, Term.pi Term.sort Term.sort])

theorem apply_function_arg_in_empty :
    HasType []
      (Term.lam (Term.pi Term.sort Term.sort) (Term.app (Term.var 0) Term.sort))
      (Term.pi (Term.pi Term.sort Term.sort) (substitute 0 Term.sort Term.sort)) := by
  apply HasType.lamRule
  · apply HasType.piRule
    · exact HasType.sortRule []
    · exact HasType.sortRule [Term.sort]
  · exact app_pi_ctx_to_sort

/-- 单 sort ctx 下: app (lam sort (var 0)) (pi (var 0) sort) 类型为 sort. -/
theorem app_id_pi_var_sort_in_sort_ctx :
    HasType [Term.sort]
      (Term.app (Term.lam Term.sort (Term.var 0)) (Term.pi (Term.var 0) Term.sort))
      Term.sort := by
  exact HasType.appRule [Term.sort] (Term.lam Term.sort (Term.var 0))
    (Term.pi (Term.var 0) Term.sort) Term.sort Term.sort
    (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
      (HasType.sortRule [Term.sort])
      (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
    pi_var_sort_in_sort_ctx

theorem pi_var_sort_then_sort_id_app_in_sort_ctx :
    HasType [Term.sort] (Term.pi (Term.var 0) Term.sort) Term.sort →
    HasType [Term.sort]
      (Term.app (Term.lam Term.sort (Term.var 0)) (Term.pi (Term.var 0) Term.sort))
      (substitute 0 (Term.pi (Term.var 0) Term.sort) Term.sort) := by
  intro hpi
  exact HasType.appRule [Term.sort] (Term.lam Term.sort (Term.var 0))
    (Term.pi (Term.var 0) Term.sort) Term.sort Term.sort
    (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
      (HasType.sortRule [Term.sort])
      (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
    hpi

theorem apply_function_arg_in_value_ctx :
    HasType [Term.var 1, Term.sort]
      (Term.lam (Term.pi (Term.var 1) Term.sort)
        (Term.app (Term.var 0) (Term.var 1)))
      (Term.pi (Term.pi (Term.var 1) Term.sort) Term.sort) := by
  apply HasType.lamRule
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · exact HasType.sortRule _
  · exact HasType.appRule
      [Term.pi (Term.var 2) Term.sort, Term.var 1, Term.sort]
      (Term.var 0)
      (Term.var 1)
      (Term.var 2)
      Term.sort
      (HasType.varRule
        [Term.pi (Term.var 2) Term.sort, Term.var 1, Term.sort]
        0
        (Term.pi (Term.var 2) Term.sort)
        rfl)
      (HasType.varRule
        [Term.pi (Term.var 2) Term.sort, Term.var 1, Term.sort]
        1
        (Term.var 2)
        rfl)

theorem dep_pi_app :
    HasType [Term.pi Term.sort (Term.var 2), Term.sort]
      (Term.app (Term.var 0) (Term.var 1))
      (Term.var 1) := by
  exact HasType.appRule
    [Term.pi Term.sort (Term.var 2), Term.sort]
    (Term.var 0)
    (Term.var 1)
    Term.sort
    (Term.var 2)
    (HasType.varRule
      [Term.pi Term.sort (Term.var 2), Term.sort]
      0
      (Term.pi Term.sort (Term.var 2))
      rfl)
    (HasType.varRule
      [Term.pi Term.sort (Term.var 2), Term.sort]
      1
      Term.sort
      rfl)

theorem apply_function_arg :
    HasType []
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.pi (Term.var 1) Term.sort)
            (Term.app (Term.var 0) (Term.var 1)))))
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi (Term.pi (Term.var 1) Term.sort) Term.sort))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · exact apply_function_arg_in_value_ctx

theorem ignore_arg :
    HasType []
      (Term.lam Term.sort (Term.lam (Term.var 0) (Term.lam Term.sort (Term.var 0))))
      (Term.pi Term.sort (Term.pi (Term.var 0) (Term.pi Term.sort Term.sort))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · exact HasType.sortRule [Term.var 1, Term.sort]
      · apply HasType.varRule
        rfl

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

theorem double_poly_first :
    HasType []
      (Term.lam Term.sort
        (Term.lam Term.sort
          (Term.lam (Term.var 1)
            (Term.lam (Term.var 1)
              (Term.var 1)))))
      (Term.pi Term.sort
        (Term.pi Term.sort
          (Term.pi (Term.var 1)
            (Term.pi (Term.var 1) (Term.var 3))))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.lamRule
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

theorem applied_poly_id :
    HasType []
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.app
            (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
              (Term.var 1))
            (Term.var 0))))
      (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · exact HasType.appRule
        [Term.var 1, Term.sort]
        (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
          (Term.var 1))
        (Term.var 0)
        (Term.var 1)
        (Term.var 2)
        (HasType.appRule
          [Term.var 1, Term.sort]
          (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
          (Term.var 1)
          Term.sort
          (Term.pi (Term.var 0) (Term.var 1))
          (HasType.lamRule
            [Term.var 1, Term.sort]
            Term.sort
            (Term.lam (Term.var 0) (Term.var 0))
            (Term.pi (Term.var 0) (Term.var 1))
            (HasType.sortRule [Term.var 1, Term.sort])
            (HasType.lamRule
              [Term.sort, Term.var 1, Term.sort]
              (Term.var 0)
              (Term.var 0)
              (Term.var 1)
              (HasType.varRule [Term.sort, Term.var 1, Term.sort]
                0 Term.sort rfl)
              (HasType.varRule [Term.var 1, Term.sort, Term.var 1, Term.sort]
                0 (Term.var 1) rfl)))
          (HasType.varRule [Term.var 1, Term.sort] 1 Term.sort rfl))
        (HasType.varRule [Term.var 1, Term.sort] 0 (Term.var 1) rfl)

theorem pi_function_to_sort_in_empty :
    HasType []
      (Term.pi (Term.pi Term.sort Term.sort) Term.sort)
      Term.sort := by
  apply HasType.piRule
  · exact pi_sort_sort_in_empty_ctx
  · exact HasType.sortRule [Term.pi Term.sort Term.sort]

theorem var_in_quint_sort :
    HasType [Term.sort, Term.sort, Term.sort, Term.sort, Term.sort] (Term.var 4) Term.sort := by
  apply HasType.varRule
  rfl

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


end BEDC.MetaCIC
