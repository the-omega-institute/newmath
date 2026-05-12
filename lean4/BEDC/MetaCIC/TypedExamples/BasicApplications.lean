import BEDC.MetaCIC.TypedExamples

namespace BEDC.MetaCIC

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
theorem applied_const_sort :
    HasType [Term.sort]
      (Term.app (Term.lam Term.sort Term.sort) Term.sort)
      Term.sort := by
  exact HasType.appRule [Term.sort] (Term.lam Term.sort Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.lamRule [Term.sort] Term.sort Term.sort Term.sort
      (HasType.sortRule [Term.sort])
      (HasType.sortRule [Term.sort, Term.sort]))
    (HasType.sortRule [Term.sort])

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



end BEDC.MetaCIC
