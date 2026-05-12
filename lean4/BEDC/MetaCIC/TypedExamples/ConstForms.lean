import BEDC.MetaCIC.TypedExamples.PiForms

namespace BEDC.MetaCIC

theorem app_const_sort_in_empty_ctx :
    HasType [] (Term.app (Term.lam Term.sort Term.sort) Term.sort) Term.sort := by
  exact HasType.appRule [] (Term.lam Term.sort Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))
    (HasType.sortRule [])

theorem const_sort_app :
    HasType [] (Term.app (Term.lam Term.sort Term.sort) Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule [] (Term.lam Term.sort Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))
    (HasType.sortRule [])

/-- 空 ctx 下: lam sort (lam sort sort) 类型为 pi sort (pi sort sort). -/
theorem double_lam_const :
    HasType [] (Term.lam Term.sort (Term.lam Term.sort Term.sort))
      (Term.pi Term.sort (Term.pi Term.sort Term.sort)) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · exact HasType.sortRule [Term.sort, Term.sort]

/-- 空 ctx 下: app (lam sort (lam sort sort)) sort 类型为 pi sort sort. -/
theorem double_lam_const_first_app :
    HasType [] (Term.app (Term.lam Term.sort (Term.lam Term.sort Term.sort)) Term.sort)
      (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule [] (Term.lam Term.sort (Term.lam Term.sort Term.sort))
    Term.sort Term.sort (Term.pi Term.sort Term.sort)
    double_lam_const
    (HasType.sortRule [])

/-- 空 ctx 下: app (app (lam sort (lam sort sort)) sort) sort 类型为 sort. -/
theorem double_lam_const_repeated_app :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam Term.sort Term.sort)) Term.sort)
        Term.sort)
      Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort Term.sort)) Term.sort)
    Term.sort Term.sort Term.sort
    double_lam_const_first_app
    (HasType.sortRule [])

theorem twice_applied_const :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam Term.sort Term.sort)) Term.sort)
        Term.sort)
      Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort Term.sort)) Term.sort)
    Term.sort Term.sort Term.sort
    double_lam_const_first_app
    (HasType.sortRule [])

theorem first_arg_proj :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
        Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam Term.sort (Term.var 1)))
      Term.sort Term.sort (Term.pi Term.sort Term.sort)
      (HasType.lamRule [] Term.sort (Term.lam Term.sort (Term.var 1))
        (Term.pi Term.sort Term.sort)
        (HasType.sortRule [])
        (HasType.lamRule [Term.sort] Term.sort (Term.var 1) Term.sort
          (HasType.sortRule [Term.sort])
          (HasType.varRule [Term.sort, Term.sort] 1 Term.sort rfl)))
      (HasType.sortRule []))
    (HasType.sortRule [])

theorem second_arg_proj :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
        Term.sort)
      (substitute 0 Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam Term.sort (Term.var 0)))
      Term.sort Term.sort (Term.pi Term.sort Term.sort)
      (HasType.lamRule [] Term.sort (Term.lam Term.sort (Term.var 0))
        (Term.pi Term.sort Term.sort)
        (HasType.sortRule [])
        (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
          (HasType.sortRule [Term.sort])
          (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl)))
      (HasType.sortRule []))
    (HasType.sortRule [])

theorem const_sort_1_applied :
    HasType []
      (Term.app
        (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
        Term.sort)
      Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
    Term.sort Term.sort Term.sort
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam Term.sort (Term.var 0)))
      Term.sort Term.sort (Term.pi Term.sort Term.sort)
      (HasType.lamRule [] Term.sort (Term.lam Term.sort (Term.var 0))
        (Term.pi Term.sort Term.sort)
        (HasType.sortRule [])
        (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
          (HasType.sortRule [Term.sort])
          (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl)))
      (HasType.sortRule []))
    (HasType.sortRule [])

/-- 单 sort ctx 下: app (lam sort (var 0)) (var 0) 类型为 sort. -/

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


end BEDC.MetaCIC
