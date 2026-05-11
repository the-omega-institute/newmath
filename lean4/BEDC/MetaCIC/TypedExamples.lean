import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

/-! 典型 typed terms 集合, 演示 shift-aware substrate 的类型 derivation. -/

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

/-- 在 [sort] ctx 下: pi (var 0) sort 类型为 sort. -/
theorem pi_var_sort_in_sort_ctx :
    HasType [Term.sort] (Term.pi (Term.var 0) Term.sort) Term.sort := by
  apply HasType.piRule
  · exact var_zero_in_sort_ctx
  · exact HasType.sortRule _

/-- 在 [sort] ctx 下: lam (var 0) (var 0) 类型为 pi (var 0) (var 1). 这是 dependent identity. -/
theorem lam_dependent_identity :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_id_outer_tracking

/-- 空 ctx 下: pi sort sort 类型为 sort. -/
theorem pi_sort_sort_in_empty_ctx :
    HasType [] (Term.pi Term.sort Term.sort) Term.sort := by
  exact pi_sort_sort_well_typed

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

/-- 单 sort ctx 下: pi (var 0) (pi (var 1) sort) 类型为 sort. -/
theorem nested_pi_dep_in_sort_ctx :
    HasType [Term.sort] (Term.pi (Term.var 0) (Term.pi (Term.var 1) Term.sort))
      Term.sort := by
  apply HasType.piRule
  · apply HasType.varRule
    rfl
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · exact HasType.sortRule [Term.var 2, Term.var 1, Term.sort]

/-- 空 ctx 下: app (lam sort (var 0)) sort 类型为 sort. -/
theorem app_id_sort_in_empty_ctx :
    HasType [] (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.var 0))
    Term.sort Term.sort Term.sort
    id_sort_well_typed
    (HasType.sortRule [])

/-- 空 ctx 下: app (lam sort sort) sort 类型为 sort. -/
theorem app_const_sort_in_empty_ctx :
    HasType [] (Term.app (Term.lam Term.sort Term.sort) Term.sort) Term.sort := by
  exact HasType.appRule [] (Term.lam Term.sort Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))
    (HasType.sortRule [])

/-- 单 sort ctx 下: app (lam sort (var 0)) (var 0) 类型为 sort. -/
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

end BEDC.MetaCIC
