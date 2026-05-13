import BEDC.HostBridge.MetaCICTransport
import BEDC.MetaCIC.Normalization
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Decidable.NormalEqDecide

namespace BEDC.HostBridge

open BEDC.MetaCIC

namespace EquationalLaws

abbrev idAppSort : Term :=
  Term.app (Term.lam Term.sort (Term.var 0)) Term.sort

abbrev fnSortToSortApp : Term :=
  Term.app
    (Term.lam Term.sort
      (Term.pi (Term.var 0) (Term.var 1)))
    Term.sort

abbrev constSortApp : Term :=
  Term.app (Term.lam Term.sort Term.sort) Term.sort

abbrev innerSortIdLam : Term :=
  Term.lam Term.sort
    (Term.app
      (Term.lam Term.sort (Term.var 0))
      (Term.var 0))

abbrev appRightIdSort : Term :=
  Term.app
    (Term.lam Term.sort Term.sort)
    idAppSort

abbrev polyIdentityApplySort : Term :=
  Term.app
    (Term.app
      (Term.lam Term.sort
        (Term.lam (Term.var 0) (Term.var 0)))
      Term.sort)
    Term.sort

abbrev churchTrueApplySort : Term :=
  Term.app
    (Term.app
      (Term.app MetaCICTransport.Meta.churchTrue Term.sort)
      Term.sort)
    Term.sort

abbrev churchFalseApplySort : Term :=
  Term.app
    (Term.app
      (Term.app MetaCICTransport.Meta.churchFalse Term.sort)
      Term.sort)
    Term.sort

abbrev churchConstApplySort : Term :=
  Term.app
    (Term.app
      (Term.app
        (Term.app MetaCICTransport.Meta.const Term.sort)
        Term.sort)
      Term.sort)
    Term.sort

abbrev idFunctionSort : Term :=
  Term.lam Term.sort (Term.var 0)

abbrev churchZeroApplySort : Term :=
  Term.app
    (Term.app
      (Term.app MetaCICTransport.Meta.churchZero Term.sort)
      idFunctionSort)
    Term.sort

abbrev churchOneApplySort : Term :=
  Term.app
    (Term.app
      (Term.app MetaCICTransport.Meta.churchOne Term.sort)
      idFunctionSort)
    Term.sort

abbrev churchSuccZeroApplySort : Term :=
  Term.app
    (Term.app
      (Term.app
        (Term.app MetaCICTransport.Meta.churchSucc
          MetaCICTransport.Meta.churchZero)
        Term.sort)
      idFunctionSort)
    Term.sort

abbrev nestedLeftRightRedex : Term :=
  Term.app
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      idAppSort)
    idAppSort

abbrev betaThenInnerLamRedex : Term :=
  Term.app
    (Term.lam Term.sort
      (Term.lam Term.sort
        (Term.app
          (Term.lam Term.sort (Term.var 0))
          (Term.var 0))))
    Term.sort

abbrev betaThenInnerLamNormal : Term :=
  Term.lam Term.sort (Term.var 0)

abbrev piDomainIdRedex : Term :=
  Term.pi idAppSort Term.sort

abbrev piCodomainIdRedex : Term :=
  Term.pi Term.sort
    (Term.app
      (Term.lam Term.sort (Term.var 0))
      (Term.var 0))

abbrev appLeftProjectionRedex : Term :=
  Term.app
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 0)))
      Term.sort)
    Term.sort

end EquationalLaws

open EquationalLaws

theorem normalize_id_app_sort :
    BEDC.MetaCIC.normalizeBounded 1
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) = Term.sort := by
  rfl

theorem normalize_id_app_sort_alias :
    BEDC.MetaCIC.normalizeBounded 1 idAppSort = Term.sort := by
  rfl

theorem host_id_app_sort :
    MetaCICTransport.Host.idSortRedex = Type := by
  rfl

theorem normalize_fn_sort_to_sort_app :
    BEDC.MetaCIC.normalizeBounded 1 fnSortToSortApp =
      Term.pi Term.sort Term.sort := by
  rfl

theorem host_fn_sort_to_sort_app :
    MetaCICTransport.Host.fnSortToSortRedex = (Type → Type) := by
  rfl

theorem normalize_const_sort_app :
    BEDC.MetaCIC.normalizeBounded 1 constSortApp = Term.sort := by
  rfl

theorem host_const_sort_app :
    MetaCICTransport.Host.constSortRedex = Type := by
  rfl

theorem normalize_inner_sort_id_lam :
    BEDC.MetaCIC.normalizeBounded 2 innerSortIdLam =
      Term.lam Term.sort (Term.var 0) := by
  rfl

theorem host_inner_sort_id_lam :
    MetaCICTransport.Host.innerSortIdRedex =
      (fun X : Type => X) := by
  rfl

theorem normalize_app_right_id_sort :
    BEDC.MetaCIC.normalizeBounded 2 appRightIdSort = Term.sort := by
  rfl

theorem host_app_right_id_sort :
    MetaCICTransport.Host.appRightIdSortRedex = Type := by
  rfl

theorem normalize_poly_identity_apply :
    BEDC.MetaCIC.normalizeBounded 2 polyIdentityApplySort = Term.sort := by
  rfl

theorem host_poly_identity_apply :
    MetaCICTransport.Host.polyIdTwoStepRedex = Type := by
  rfl

theorem normalize_church_true_apply :
    BEDC.MetaCIC.normalizeBounded 4 churchTrueApplySort = Term.sort := by
  rfl

theorem host_church_true_apply :
    MetaCICTransport.Host.churchTrue Unit Unit.unit Unit.unit = Unit.unit := by
  rfl

theorem normalize_church_false_apply :
    BEDC.MetaCIC.normalizeBounded 4 churchFalseApplySort = Term.sort := by
  rfl

theorem host_church_false_apply :
    MetaCICTransport.Host.churchFalse Unit Unit.unit Unit.unit = Unit.unit := by
  rfl

theorem normalize_church_const_apply :
    BEDC.MetaCIC.normalizeBounded 5 churchConstApplySort = Term.sort := by
  rfl

theorem host_church_const_apply :
    MetaCICTransport.Host.const Unit Unit Unit.unit Unit.unit = Unit.unit := by
  rfl

theorem normalize_church_zero_apply :
    BEDC.MetaCIC.normalizeBounded 4 churchZeroApplySort = Term.sort := by
  rfl

theorem host_church_zero_apply :
    MetaCICTransport.Host.churchZero Unit (fun x : Unit => x) Unit.unit = Unit.unit := by
  rfl

theorem normalize_church_one_apply :
    BEDC.MetaCIC.normalizeBounded 5 churchOneApplySort = Term.sort := by
  rfl

theorem host_church_one_apply :
    MetaCICTransport.Host.churchOne Unit (fun x : Unit => x) Unit.unit = Unit.unit := by
  rfl

theorem normalize_church_succ_zero_apply :
    BEDC.MetaCIC.normalizeBounded 6 churchSuccZeroApplySort = Term.sort := by
  rfl

theorem host_church_succ_zero_apply :
    MetaCICTransport.Host.churchSucc
      MetaCICTransport.Host.churchZero Unit (fun x : Unit => x) Unit.unit = Unit.unit := by
  rfl

theorem id_app_sort_beta_step :
    BetaStep idAppSort Term.sort := by
  exact BetaStep.beta Term.sort (Term.var 0) Term.sort

theorem id_app_sort_beta_star :
    BetaStarStep idAppSort Term.sort := by
  exact betaStarStep_single id_app_sort_beta_step

theorem fn_sort_to_sort_beta_step :
    BetaStep fnSortToSortApp (Term.pi Term.sort Term.sort) := by
  exact BetaStep.beta Term.sort
    (Term.pi (Term.var 0) (Term.var 1))
    Term.sort

theorem fn_sort_to_sort_beta_star :
    BetaStarStep fnSortToSortApp (Term.pi Term.sort Term.sort) := by
  exact betaStarStep_single fn_sort_to_sort_beta_step

theorem const_sort_beta_step :
    BetaStep constSortApp Term.sort := by
  exact BetaStep.beta Term.sort Term.sort Term.sort

theorem const_sort_beta_star :
    BetaStarStep constSortApp Term.sort := by
  exact betaStarStep_single const_sort_beta_step

theorem inner_sort_id_lam_beta_step :
    BetaStep innerSortIdLam (Term.lam Term.sort (Term.var 0)) := by
  exact BetaStep.congLam Term.sort
    (Term.app
      (Term.lam Term.sort (Term.var 0))
      (Term.var 0))
    (Term.var 0)
    (BetaStep.beta Term.sort (Term.var 0) (Term.var 0))

theorem inner_sort_id_lam_beta_star :
    BetaStarStep innerSortIdLam (Term.lam Term.sort (Term.var 0)) := by
  exact betaStarStep_single inner_sort_id_lam_beta_step

theorem app_right_id_sort_first_step :
    BetaStep appRightIdSort constSortApp := by
  exact BetaStep.congApp2
    (Term.lam Term.sort Term.sort)
    idAppSort
    Term.sort
    id_app_sort_beta_step

theorem app_right_id_sort_chain :
    BetaStarStep appRightIdSort Term.sort := by
  exact betaStarStep_of_two_steps
    app_right_id_sort_first_step
    const_sort_beta_step

theorem poly_identity_first_step :
    BetaStep polyIdentityApplySort
      (Term.app (Term.lam Term.sort (Term.var 0)) Term.sort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.lam Term.sort
        (Term.lam (Term.var 0) (Term.var 0)))
      Term.sort)
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    (BetaStep.beta Term.sort
      (Term.lam (Term.var 0) (Term.var 0))
      Term.sort)

theorem poly_identity_chain :
    BetaStarStep polyIdentityApplySort Term.sort := by
  exact betaStarStep_of_two_steps
    poly_identity_first_step
    id_app_sort_beta_step

theorem church_true_apply_step_one :
    BetaStep churchTrueApplySort
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 1)))
          Term.sort)
        Term.sort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.app MetaCICTransport.Meta.churchTrue Term.sort)
      Term.sort)
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      Term.sort)
    Term.sort
    (BetaStep.congApp1
      (Term.app MetaCICTransport.Meta.churchTrue Term.sort)
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      Term.sort
      (BetaStep.beta Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1) (Term.var 1)))
        Term.sort))

theorem church_true_apply_step_two :
    BetaStep
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 1)))
          Term.sort)
        Term.sort)
      (Term.app
        (Term.lam Term.sort Term.sort)
        Term.sort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      Term.sort)
    (Term.lam Term.sort Term.sort)
    Term.sort
    (BetaStep.beta Term.sort
      (Term.lam Term.sort (Term.var 1))
      Term.sort)

theorem church_true_apply_chain :
    BetaStarStep churchTrueApplySort Term.sort := by
  exact betaStarStep_three_steps
    church_true_apply_step_one
    church_true_apply_step_two
    const_sort_beta_step

theorem church_false_apply_step_one :
    BetaStep churchFalseApplySort
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 0)))
          Term.sort)
        Term.sort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.app MetaCICTransport.Meta.churchFalse Term.sort)
      Term.sort)
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 0)))
      Term.sort)
    Term.sort
    (BetaStep.congApp1
      (Term.app MetaCICTransport.Meta.churchFalse Term.sort)
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 0)))
      Term.sort
      (BetaStep.beta Term.sort
        (Term.lam (Term.var 0)
          (Term.lam (Term.var 1) (Term.var 0)))
        Term.sort))

theorem church_false_apply_step_two :
    BetaStep
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 0)))
          Term.sort)
        Term.sort)
      idAppSort := by
  exact BetaStep.congApp1
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 0)))
      Term.sort)
    (Term.lam Term.sort (Term.var 0))
    Term.sort
    (BetaStep.beta Term.sort
      (Term.lam Term.sort (Term.var 0))
      Term.sort)

theorem church_false_apply_chain :
    BetaStarStep churchFalseApplySort Term.sort := by
  exact betaStarStep_three_steps
    church_false_apply_step_one
    church_false_apply_step_two
    id_app_sort_beta_step

theorem nested_left_right_first_step :
    BetaStep nestedLeftRightRedex
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 1)))
          Term.sort)
        idAppSort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      idAppSort)
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      Term.sort)
    idAppSort
    (BetaStep.congApp2
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      idAppSort
      Term.sort
      id_app_sort_beta_step)

theorem nested_left_right_second_step :
    BetaStep
      (Term.app
        (Term.app
          (Term.lam Term.sort
            (Term.lam Term.sort (Term.var 1)))
          Term.sort)
        idAppSort)
      (Term.app (Term.lam Term.sort Term.sort) idAppSort) := by
  exact BetaStep.congApp1
    (Term.app
      (Term.lam Term.sort
        (Term.lam Term.sort (Term.var 1)))
      Term.sort)
    (Term.lam Term.sort Term.sort)
    idAppSort
    (BetaStep.beta Term.sort
      (Term.lam Term.sort (Term.var 1))
      Term.sort)

theorem nested_left_right_third_step :
    BetaStep
      (Term.app (Term.lam Term.sort Term.sort) idAppSort)
      constSortApp := by
  exact BetaStep.congApp2
    (Term.lam Term.sort Term.sort)
    idAppSort
    Term.sort
    id_app_sort_beta_step

theorem reduction_chain_example :
    BetaStarStep nestedLeftRightRedex Term.sort := by
  exact betaStarStep_triple
    (betaStarStep_three_steps
      nested_left_right_first_step
      nested_left_right_second_step
      nested_left_right_third_step)
    const_sort_beta_star
    (BetaStarStep.refl Term.sort)

theorem beta_then_inner_lam_first_step :
    BetaStep betaThenInnerLamRedex
      (Term.lam Term.sort
        (Term.app
          (Term.lam Term.sort (Term.var 0))
          (Term.var 0))) := by
  exact BetaStep.beta Term.sort
    (Term.lam Term.sort
      (Term.app
        (Term.lam Term.sort (Term.var 0))
        (Term.var 0)))
    Term.sort

theorem beta_then_inner_lam_chain :
    BetaStarStep betaThenInnerLamRedex betaThenInnerLamNormal := by
  exact betaStarStep_of_two_steps
    beta_then_inner_lam_first_step
    inner_sort_id_lam_beta_step

theorem pi_domain_id_chain :
    BetaStarStep piDomainIdRedex (Term.pi Term.sort Term.sort) := by
  exact betaStarStep_single
    (BetaStep.congPiDom idAppSort Term.sort Term.sort
      id_app_sort_beta_step)

theorem pi_codomain_id_chain :
    BetaStarStep piCodomainIdRedex
      (Term.pi Term.sort (Term.var 0)) := by
  exact betaStarStep_single
    (BetaStep.congPiCod Term.sort
      (Term.app
        (Term.lam Term.sort (Term.var 0))
        (Term.var 0))
      (Term.var 0)
      (BetaStep.beta Term.sort (Term.var 0) (Term.var 0)))

theorem app_left_projection_chain :
    BetaStarStep appLeftProjectionRedex Term.sort := by
  exact betaStarStep_of_two_steps
    (BetaStep.congApp1
      (Term.app
        (Term.lam Term.sort
          (Term.lam Term.sort (Term.var 0)))
        Term.sort)
      (Term.lam Term.sort (Term.var 0))
      Term.sort
      (BetaStep.beta Term.sort
        (Term.lam Term.sort (Term.var 0))
        Term.sort))
    id_app_sort_beta_step

end BEDC.HostBridge
