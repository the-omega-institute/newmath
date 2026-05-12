import BEDC.MetaCIC.TypedExamples

namespace BEDC.MetaCIC

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
theorem app_id_var_in_sort_ctx :
    HasType [Term.sort] (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))
      Term.sort := by
  exact HasType.appRule [Term.sort] (Term.lam Term.sort (Term.var 0))
    (Term.var 0) Term.sort Term.sort
    (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
      (HasType.sortRule [Term.sort])
      (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
    (HasType.varRule [Term.sort] 0 Term.sort rfl)


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

theorem second_proj :
    HasType []
      (Term.lam Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1) (Term.var 0))))
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi (Term.var 1) (Term.var 2)))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl


end BEDC.MetaCIC
