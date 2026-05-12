import BEDC.MetaCIC.TypedExamples.Identity
import BEDC.MetaCIC.TypedExamples.ConstForms

namespace BEDC.MetaCIC

theorem id_applied_to_sort_type :
    HasType []
      (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
      (substitute 0 Term.sort (Term.pi (Term.var 0) (Term.var 1))) := by
  exact HasType.appRule []
    (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
    Term.sort
    Term.sort
    (Term.pi (Term.var 0) (Term.var 1))
    polymorphic_identity
    (HasType.sortRule [])

theorem poly_id_at_sort_full :
    HasType []
      (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
      (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
    Term.sort
    Term.sort
    (Term.pi (Term.var 0) (Term.var 1))
    polymorphic_identity
    (HasType.sortRule [])

theorem poly_id_double_app :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
        Term.sort)
      Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
    Term.sort
    Term.sort
    Term.sort
    poly_id_at_sort_full
    (HasType.sortRule [])

theorem poly_id_to_pi_type :
    HasType []
      (Term.app (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
        (Term.pi Term.sort Term.sort))
        (Term.lam Term.sort Term.sort))
      (substitute 0 (Term.lam Term.sort Term.sort) (Term.pi Term.sort Term.sort)) := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
      (Term.pi Term.sort Term.sort))
    (Term.lam Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
      (Term.pi Term.sort Term.sort)
      Term.sort
      (Term.pi (Term.var 0) (Term.var 1))
      polymorphic_identity
      pi_sort_sort_in_empty_ctx)
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))

/-- 空 ctx 下: lambda 内构造 pi (var 0) (var 1), 外层类型为 pi sort sort. -/

theorem app_id_sort_in_empty_ctx :
    HasType [] (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.var 0))
    Term.sort Term.sort Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

theorem id_to_id_in_empty :
    HasType []
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      Term.sort := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.var 0))
    Term.sort Term.sort Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

/-- 空 ctx 下: app (lam sort (pi (var 0) sort)) sort 类型为 sort. -/
theorem applied_pi_constructor_in_empty :
    HasType []
      (Term.app (Term.lam Term.sort (Term.pi (Term.var 0) Term.sort)) Term.sort)
      Term.sort := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.pi (Term.var 0) Term.sort))
    Term.sort Term.sort Term.sort
    (HasType.lamRule [] Term.sort (Term.pi (Term.var 0) Term.sort) Term.sort
      (HasType.sortRule [])
      (HasType.piRule [Term.sort] (Term.var 0) Term.sort
        (HasType.varRule [Term.sort] 0 Term.sort rfl)
        (HasType.sortRule [Term.var 1, Term.sort])))
    (HasType.sortRule [])

theorem applied_pi_constructor_in_empty_result_eq :
    substitute 0 Term.sort (Term.pi (Term.var 0) Term.sort) =
      Term.pi Term.sort Term.sort := by
  rfl

/-- 空 ctx 下: app (lam sort (var 0)) (pi sort sort) 类型为 sort. -/
theorem id_applied_to_pi :
    HasType []
      (Term.app (Term.lam Term.sort (Term.var 0)) (Term.pi Term.sort Term.sort))
      Term.sort := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort) Term.sort Term.sort
    id_sort_well_typed
    pi_sort_sort_in_empty_ctx

theorem id_applied_pi_value :
    HasType []
      (Term.app (Term.lam Term.sort (Term.var 0)) (Term.pi Term.sort Term.sort))
      (substitute 0 (Term.pi Term.sort Term.sort) Term.sort) := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.var 0))
    (Term.pi Term.sort Term.sort) Term.sort Term.sort
    id_sort_well_typed
    pi_sort_sort_in_empty_ctx

theorem id_applied_to_pi_result_eq :
    substitute 0 (Term.pi Term.sort Term.sort) (Term.var 0) =
      Term.pi Term.sort Term.sort := by
  rfl

/-- 空 ctx 下: lam (pi sort sort) (var 0) 是 pi-type values 上的 identity. -/
theorem id_on_pi_sort_sort :
    HasType []
      (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
      (Term.pi (Term.pi Term.sort Term.sort) (Term.pi Term.sort Term.sort)) := by
  apply HasType.lamRule
  · apply HasType.piRule
    · exact HasType.sortRule []
    · exact HasType.sortRule [Term.sort]
  · apply HasType.varRule
    rfl

theorem pi_value_id :
    HasType []
      (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
      (Term.pi (Term.pi Term.sort Term.sort) (Term.pi Term.sort Term.sort)) := by
  exact id_on_pi_sort_sort

/-- 空 ctx 下: lam (pi sort sort) (lam sort (var 0)) 给出 pi 参数后的 sort identity. -/
theorem proj_for_pi_arg :
    HasType []
      (Term.lam (Term.pi Term.sort Term.sort) (Term.lam Term.sort (Term.var 0)))
      (Term.pi (Term.pi Term.sort Term.sort) (Term.pi Term.sort Term.sort)) := by
  apply HasType.lamRule
  · apply HasType.piRule
    · exact HasType.sortRule []
    · exact HasType.sortRule [Term.sort]
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.pi Term.sort Term.sort]
    · apply HasType.varRule
      rfl

theorem identity_on_pi_type :
    HasType []
      (Term.app
        (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
        (Term.lam Term.sort Term.sort))
      (substitute 0 (Term.lam Term.sort Term.sort) (Term.pi Term.sort Term.sort)) := by
  exact HasType.appRule []
    (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
    (Term.lam Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (HasType.lamRule [] (Term.pi Term.sort Term.sort) (Term.var 0)
      (Term.pi Term.sort Term.sort)
      pi_sort_sort_in_empty_ctx
      (HasType.varRule [Term.pi Term.sort Term.sort] 0
        (Term.pi Term.sort Term.sort) rfl))
      (HasType.lamRule [] Term.sort Term.sort Term.sort
        (HasType.sortRule [])
        (HasType.sortRule [Term.sort]))

theorem id_for_pi_applied :
    HasType []
      (Term.app (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
        (Term.lam Term.sort Term.sort))
      (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.lam (Term.pi Term.sort Term.sort) (Term.var 0))
    (Term.lam Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (Term.pi Term.sort Term.sort)
    (HasType.lamRule [] (Term.pi Term.sort Term.sort) (Term.var 0)
      (Term.pi Term.sort Term.sort)
      pi_sort_sort_in_empty_ctx
      (HasType.varRule [Term.pi Term.sort Term.sort] 0
        (Term.pi Term.sort Term.sort) rfl))
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))

/-- 空 ctx 下: app (lam sort sort) sort 类型为 sort. -/

theorem app_id_var_in_sort_ctx :
    HasType [Term.sort] (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))
      Term.sort := by
  exact HasType.appRule [Term.sort] (Term.lam Term.sort (Term.var 0))
    (Term.var 0) Term.sort Term.sort
    (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
      (HasType.sortRule [Term.sort])
      (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
    (HasType.varRule [Term.sort] 0 Term.sort rfl)

theorem dep_id_applied_to_arg_in_sort_ctx (a : Term) :
    HasType [Term.sort] a (Term.var 0) →
    HasType [Term.sort]
      (Term.app (Term.lam (Term.var 0) (Term.var 0)) a)
      (substitute 0 a (Term.var 1)) := by
  intro ha
  exact HasType.appRule [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
    a (Term.var 0) (Term.var 1)
    lam_dependent_identity
    ha

theorem dep_id_applied_to_arg_result_in_sort_ctx (a : Term) :
    HasType [Term.sort] a (Term.var 0) →
    HasType [Term.sort]
      (Term.app (Term.lam (Term.var 0) (Term.var 0)) a)
      (Term.var 0) := by
  intro ha
  exact HasType.appRule [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
    a (Term.var 0) (Term.var 1)
    lam_dependent_identity
    ha

/-- 双 sort ctx 下: dependent identity 应用于满足同一 domain 的 var 0. -/
theorem applied_dep_id_in_double_sort_ctx :
    HasType [Term.sort, Term.sort] (Term.var 0) (Term.var 0) →
    HasType [Term.sort, Term.sort]
      (Term.app (Term.lam (Term.var 0) (Term.var 0)) (Term.var 0))
      (Term.var 0) := by
  intro harg
  exact HasType.appRule [Term.sort, Term.sort]
    (Term.lam (Term.var 0) (Term.var 0))
    (Term.var 0) (Term.var 0) (Term.var 1)
    (HasType.lamRule [Term.sort, Term.sort]
      (Term.var 0) (Term.var 0) (Term.var 1)
      (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl)
      (HasType.varRule [Term.var 1, Term.sort, Term.sort] 0 (Term.var 1) rfl))
    harg

/-- 单 sort ctx 下: app (lam sort sort) sort 类型为 sort. -/

theorem app_with_pi_context :
    HasType [Term.pi Term.sort Term.sort]
      (Term.app (Term.lam Term.sort (Term.var 1)) Term.sort)
      (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule [Term.pi Term.sort Term.sort]
    (Term.lam Term.sort (Term.var 1))
    Term.sort
    Term.sort
    (Term.pi Term.sort Term.sort)
    (HasType.lamRule [Term.pi Term.sort Term.sort] Term.sort (Term.var 1)
      (Term.pi Term.sort Term.sort)
      (HasType.sortRule [Term.pi Term.sort Term.sort])
      (HasType.varRule [Term.sort, Term.pi Term.sort Term.sort] 1
        (Term.pi Term.sort Term.sort) rfl))
    (HasType.sortRule [Term.pi Term.sort Term.sort])

/-- pi sort sort ctx 下: var 0 作为函数应用到 sort, 结果类型为 sort。 -/
theorem app_pi_var_to_sort :
    HasType [Term.pi Term.sort Term.sort]
      (Term.app (Term.var 0) Term.sort)
      Term.sort := by
  exact HasType.appRule [Term.pi Term.sort Term.sort]
    (Term.var 0)
    Term.sort
    Term.sort
    Term.sort
    (HasType.varRule [Term.pi Term.sort Term.sort] 0
      (Term.pi Term.sort Term.sort) rfl)
    (HasType.sortRule [Term.pi Term.sort Term.sort])

theorem app_pi_function :
    HasType [Term.pi Term.sort Term.sort, Term.sort]
      (Term.app (Term.var 0) Term.sort)
      Term.sort := by
  exact HasType.appRule [Term.pi Term.sort Term.sort, Term.sort]
    (Term.var 0)
    Term.sort
    Term.sort
    Term.sort
    (HasType.varRule [Term.pi Term.sort Term.sort, Term.sort] 0
      (Term.pi Term.sort Term.sort) rfl)
    (HasType.sortRule [Term.pi Term.sort Term.sort, Term.sort])

theorem app_pi_ctx_to_sort :
    HasType [Term.pi Term.sort Term.sort]
      (Term.app (Term.var 0) Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule [Term.pi Term.sort Term.sort]
    (Term.var 0)
    Term.sort
    Term.sort
    Term.sort
    (HasType.varRule [Term.pi Term.sort Term.sort] 0
      (Term.pi Term.sort Term.sort) rfl)
    (HasType.sortRule [Term.pi Term.sort Term.sort])

theorem app_two_pi_vars :
    HasType [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
      (Term.app (Term.var 0) Term.sort)
      Term.sort ∧
    HasType [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
      (Term.app (Term.var 1) Term.sort)
      Term.sort := by
  constructor
  · exact HasType.appRule
      [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
      (Term.var 0)
      Term.sort
      Term.sort
      Term.sort
      (HasType.varRule
        [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
        0
        (Term.pi Term.sort Term.sort)
        rfl)
      (HasType.sortRule
        [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort])
  · exact HasType.appRule
      [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
      (Term.var 1)
      Term.sort
      Term.sort
      Term.sort
      (HasType.varRule
        [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort]
        1
        (Term.pi Term.sort Term.sort)
        rfl)
      (HasType.sortRule
        [Term.pi Term.sort Term.sort, Term.pi Term.sort Term.sort])

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


end BEDC.MetaCIC
