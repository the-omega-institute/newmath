import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Confluence.Core

namespace BEDC.MetaCIC

theorem id_sort_redex : BetaStep
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort := by
  exact BetaStep.beta Term.sort (Term.var 0) Term.sort

theorem id_sort_redex_typed : HasType []
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort := by
  exact id_sort_applied

theorem fn_sort_to_sort_redex : BetaStep
    (Term.app (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1))) Term.sort)
    (Term.pi Term.sort Term.sort) := by
  exact BetaStep.beta Term.sort (Term.pi (Term.var 0) (Term.var 1)) Term.sort

theorem fn_sort_to_sort_redex_typed : HasType []
    (Term.app (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1))) Term.sort)
    Term.sort := by
  exact HasType.appRule []
    (Term.lam Term.sort (Term.pi (Term.var 0) (Term.var 1)))
    Term.sort
    Term.sort
    Term.sort
    (HasType.lamRule [] Term.sort (Term.pi (Term.var 0) (Term.var 1)) Term.sort
      (HasType.sortRule [])
      (HasType.piRule [Term.sort] (Term.var 0) (Term.var 1)
        (HasType.varRule [Term.sort] 0 Term.sort rfl)
        (HasType.varRule [Term.var 1, Term.sort] 1 Term.sort rfl)))
    (HasType.sortRule [])

theorem const_sort_redex : BetaStep
    (Term.app (Term.lam Term.sort Term.sort) Term.sort)
    Term.sort := by
  exact BetaStep.beta Term.sort Term.sort Term.sort

theorem const_sort_redex_typed : HasType []
    (Term.app (Term.lam Term.sort Term.sort) Term.sort)
    Term.sort := by
  exact HasType.appRule []
    (Term.lam Term.sort Term.sort)
    Term.sort
    Term.sort
    Term.sort
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))
    (HasType.sortRule [])

theorem inner_id_redex : BetaStep
    (Term.lam Term.sort (Term.app (Term.lam (Term.var 0) (Term.var 0)) (Term.var 0)))
    (Term.lam Term.sort (Term.var 0)) := by
  exact BetaStep.congLam Term.sort
    (Term.app (Term.lam (Term.var 0) (Term.var 0)) (Term.var 0))
    (Term.var 0)
    (BetaStep.beta (Term.var 0) (Term.var 0) (Term.var 0))

theorem inner_sort_id_redex : BetaStep
    (Term.lam Term.sort (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0)))
    (Term.lam Term.sort (Term.var 0)) := by
  exact BetaStep.congLam Term.sort
    (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))
    (Term.var 0)
    (BetaStep.beta Term.sort (Term.var 0) (Term.var 0))

theorem inner_sort_id_redex_typed : HasType []
    (Term.lam Term.sort (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0)))
    (Term.pi Term.sort Term.sort) := by
  apply HasType.lamRule
  · exact HasType.sortRule []
  · exact HasType.appRule [Term.sort]
      (Term.lam Term.sort (Term.var 0))
      (Term.var 0)
      Term.sort
      Term.sort
      (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
        (HasType.sortRule [Term.sort])
        (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
      (HasType.varRule [Term.sort] 0 Term.sort rfl)

theorem app_right_id_sort_redex : BetaStep
    (Term.app (Term.lam Term.sort Term.sort)
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort))
    (Term.app (Term.lam Term.sort Term.sort) Term.sort) := by
  exact BetaStep.congApp2
    (Term.lam Term.sort Term.sort)
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort
    id_sort_redex

theorem app_right_id_sort_redex_typed : HasType []
    (Term.app (Term.lam Term.sort Term.sort)
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort))
    Term.sort := by
  exact HasType.appRule []
    (Term.lam Term.sort Term.sort)
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort
    Term.sort
    (HasType.lamRule [] Term.sort Term.sort Term.sort
      (HasType.sortRule [])
      (HasType.sortRule [Term.sort]))
    id_sort_redex_typed

theorem pi_domain_redex : BetaStep
    (Term.pi (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) Term.sort)
    (Term.pi Term.sort Term.sort) := by
  exact BetaStep.congPiDom
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)
    Term.sort
    Term.sort
    id_sort_redex

theorem pi_domain_redex_typed : HasType []
    (Term.pi (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) Term.sort)
    Term.sort := by
  apply HasType.piRule
  · exact id_sort_redex_typed
  · exact HasType.sortRule
      [shift 0 1 (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort)]

theorem pi_cod_redex : BetaStep
    (Term.pi Term.sort (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0)))
    (Term.pi Term.sort (Term.var 0)) := by
  exact BetaStep.congPiCod Term.sort
    (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0))
    (Term.var 0)
    (BetaStep.beta Term.sort (Term.var 0) (Term.var 0))

theorem pi_cod_redex_typed : HasType []
    (Term.pi Term.sort (Term.app (Term.lam Term.sort (Term.var 0)) (Term.var 0)))
    Term.sort := by
  apply HasType.piRule
  · exact HasType.sortRule []
  · exact HasType.appRule [Term.sort]
      (Term.lam Term.sort (Term.var 0))
      (Term.var 0)
      Term.sort
      Term.sort
      (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
        (HasType.sortRule [Term.sort])
        (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl))
      (HasType.varRule [Term.sort] 0 Term.sort rfl)

theorem poly_id_two_step_redex : BetaStarStep
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
      Term.sort)
    Term.sort := by
  exact betaStarStep_of_two_steps
    (BetaStep.congApp1
      (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
      (Term.lam Term.sort (Term.var 0))
      Term.sort
      (BetaStep.beta Term.sort (Term.lam (Term.var 0) (Term.var 0)) Term.sort))
    (BetaStep.beta Term.sort (Term.var 0) Term.sort)

theorem poly_id_two_step_redex_typed : HasType []
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
      Term.sort)
    Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) Term.sort)
    Term.sort
    Term.sort
    Term.sort
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0)))
      Term.sort
      Term.sort
      (Term.pi (Term.var 0) (Term.var 1))
      (HasType.lamRule [] Term.sort (Term.lam (Term.var 0) (Term.var 0))
        (Term.pi (Term.var 0) (Term.var 1))
        (HasType.sortRule [])
        (HasType.lamRule [Term.sort] (Term.var 0) (Term.var 0) (Term.var 1)
          (HasType.varRule [Term.sort] 0 Term.sort rfl)
          (HasType.varRule [Term.var 1, Term.sort] 0 (Term.var 1) rfl)))
      (HasType.sortRule []))
    (HasType.sortRule [])

theorem k_sort_partial_redex : BetaStep
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
    (Term.lam Term.sort Term.sort) := by
  exact BetaStep.beta Term.sort (Term.lam Term.sort (Term.var 1)) Term.sort

theorem k_sort_partial_redex_typed : HasType []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
    (Term.pi Term.sort Term.sort) := by
  exact HasType.appRule []
    (Term.lam Term.sort (Term.lam Term.sort (Term.var 1)))
    Term.sort
    Term.sort
    (Term.pi Term.sort Term.sort)
    (HasType.lamRule [] Term.sort (Term.lam Term.sort (Term.var 1))
      (Term.pi Term.sort Term.sort)
      (HasType.sortRule [])
      (HasType.lamRule [Term.sort] Term.sort (Term.var 1) Term.sort
        (HasType.sortRule [Term.sort])
        (HasType.varRule [Term.sort, Term.sort] 1 Term.sort rfl)))
    (HasType.sortRule [])

theorem k_sort_two_step_redex : BetaStarStep
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
      Term.sort)
    Term.sort := by
  exact betaStarStep_of_two_steps
    (BetaStep.congApp1
      (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
      (Term.lam Term.sort Term.sort)
      Term.sort
      k_sort_partial_redex)
    const_sort_redex

theorem k_sort_two_step_redex_typed : HasType []
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
      Term.sort)
    Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 1))) Term.sort)
    Term.sort
    Term.sort
    Term.sort
    k_sort_partial_redex_typed
    (HasType.sortRule [])

theorem app_left_projection_redex : BetaStep
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
      Term.sort)
    (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) := by
  exact BetaStep.congApp1
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    (BetaStep.beta Term.sort (Term.lam Term.sort (Term.var 0)) Term.sort)

theorem app_left_projection_redex_typed : HasType []
    (Term.app
      (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
      Term.sort)
    Term.sort := by
  exact HasType.appRule []
    (Term.app (Term.lam Term.sort (Term.lam Term.sort (Term.var 0))) Term.sort)
    Term.sort
    Term.sort
    Term.sort
    (HasType.appRule []
      (Term.lam Term.sort (Term.lam Term.sort (Term.var 0)))
      Term.sort
      Term.sort
      (Term.pi Term.sort Term.sort)
      (HasType.lamRule [] Term.sort (Term.lam Term.sort (Term.var 0))
        (Term.pi Term.sort Term.sort)
        (HasType.sortRule [])
        (HasType.lamRule [Term.sort] Term.sort (Term.var 0) Term.sort
          (HasType.sortRule [Term.sort])
          (HasType.varRule [Term.sort, Term.sort] 0 Term.sort rfl)))
      (HasType.sortRule []))
    (HasType.sortRule [])

end BEDC.MetaCIC
