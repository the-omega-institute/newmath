import BEDC.MetaCIC.TypedExamples.PiForms

namespace BEDC.MetaCIC

theorem lam_dependent_identity :
    HasType [Term.sort] (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_id_outer_tracking

theorem carrier_identity_in_sort_ctx :
    HasType [Term.sort]
      (Term.lam (Term.var 0) (Term.var 0))
      (Term.pi (Term.var 0) (Term.var 1)) := by
  exact dependent_id_outer_tracking

/-- 双 sort ctx 下, body 的 var 1 指向外层 ctx 的 var 0, 其类型为 sort。 -/
theorem lam_inner_to_outer_in_double_sort :
    HasType [Term.sort, Term.sort]
      (Term.lam (Term.var 0) (Term.var 1))
      (Term.pi (Term.var 0) Term.sort) := by
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

/-- 三 sort ctx 下同形态, body 的 var 2 指向更外层 sort 变量。 -/
theorem triple_sort_lam :
    HasType [Term.sort, Term.sort, Term.sort]
      (Term.lam (Term.var 0) (Term.var 2))
      (Term.pi (Term.var 0) Term.sort) := by
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

/-- 空 ctx 下: pi sort sort 类型为 sort. -/

theorem polymorphic_identity :
    HasType []
      (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
      (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · exact lam_dependent_identity

theorem nested_poly_id :
    HasType []
      (Term.lam Term.sort (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))))
      (Term.pi Term.sort (Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 1)))) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · exact HasType.sortRule [Term.sort]
    · apply HasType.lamRule
      · apply HasType.varRule
        rfl
      · apply HasType.varRule
        rfl


theorem lam_constructs_dependent_pi :
    HasType [] (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1)))
      (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.piRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

theorem double_lam_pi_construct :
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

theorem first_of_two :
    HasType []
      (Term.lam Term.sort
        (Term.lam (Term.var 0) (Term.lam (Term.var 1) (Term.var 1))))
      (Term.pi Term.sort
        (Term.pi (Term.var 0) (Term.pi (Term.var 1) (Term.var 2)))) := by
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

theorem second_of_two :
    HasType []
      (Term.lam Term.sort
        (Term.lam (Term.var 0) (Term.lam (Term.var 1) (Term.var 0))))
      (Term.pi Term.sort
        (Term.pi (Term.var 0) (Term.pi (Term.var 1) (Term.var 2)))) := by
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
