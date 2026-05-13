import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

theorem hasType_sort_ctx {Γ : Ctx} {A : Term}
    (h : HasType Γ Term.sort A) :
    A = Term.sort := by
  cases h
  rfl

theorem hasType_sort_empty_ctx {A : Term}
    (h : HasType [] Term.sort A) :
    A = Term.sort := by
  exact hasType_sort_ctx h

theorem hasType_var_ctx_lookup {Γ : Ctx} {i : Idx} {A : Term}
    (h : HasType Γ (Term.var i) A) :
    Ctx.lookup Γ i = some A := by
  cases h with
  | varRule Γ j B hlookup =>
      exact hlookup

theorem hasType_var_empty_ctx_absurd
    (i : Idx) (A : Term)
    (h : HasType [] (Term.var i) A) :
    False := by
  cases h with
  | varRule Γ j B hlookup =>
      cases hlookup

theorem hasType_var_empty_ctx_absurd_implicit {i : Idx} {A : Term}
    (h : HasType [] (Term.var i) A) :
    False := by
  exact hasType_var_empty_ctx_absurd i A h

theorem hasType_pi_ctx_components {Γ : Ctx} {dom cod A : Term}
    (h : HasType Γ (Term.pi dom cod) A) :
    A = Term.sort ∧
      HasType Γ dom Term.sort ∧
        HasType ((shift 0 1 dom) :: Γ) cod Term.sort := by
  cases h with
  | piRule Γ0 dom0 cod0 hdom hcod =>
      exact And.intro rfl (And.intro hdom hcod)

theorem hasType_pi_ctx_sort {Γ : Ctx} {dom cod A : Term}
    (h : HasType Γ (Term.pi dom cod) A) :
    A = Term.sort := by
  exact (hasType_pi_ctx_components h).left

theorem hasType_pi_ctx_dom {Γ : Ctx} {dom cod A : Term}
    (h : HasType Γ (Term.pi dom cod) A) :
    HasType Γ dom Term.sort := by
  exact (hasType_pi_ctx_components h).right.left

theorem hasType_pi_ctx_cod {Γ : Ctx} {dom cod A : Term}
    (h : HasType Γ (Term.pi dom cod) A) :
    HasType ((shift 0 1 dom) :: Γ) cod Term.sort := by
  exact (hasType_pi_ctx_components h).right.right

theorem hasType_app_ctx_components {Γ : Ctx} {f a A : Term}
    (h : HasType Γ (Term.app f a) A) :
    ∃ dom cod,
      A = substitute 0 a cod ∧
        HasType Γ f (Term.pi dom cod) ∧
          HasType Γ a dom := by
  cases h with
  | appRule Γ0 f0 a0 dom cod hf ha =>
      exact Exists.intro dom
        (Exists.intro cod
          (And.intro rfl (And.intro hf ha)))

theorem hasType_app_empty_ctx_pi {f a A : Term}
    (h : HasType [] (Term.app f a) A) :
    ∃ dom cod, HasType [] f (Term.pi dom cod) ∧ HasType [] a dom := by
  cases hasType_app_ctx_components h with
  | intro dom rest =>
      cases rest with
      | intro cod hcomponents =>
          exact Exists.intro dom
            (Exists.intro cod
              (And.intro hcomponents.right.left hcomponents.right.right))

theorem hasType_app_empty_ctx_result {f a A : Term}
    (h : HasType [] (Term.app f a) A) :
    ∃ dom cod,
      A = substitute 0 a cod ∧
        HasType [] f (Term.pi dom cod) ∧
          HasType [] a dom := by
  exact hasType_app_ctx_components h

theorem hasType_app_empty_ctx_left_pi {f a A : Term}
    (h : HasType [] (Term.app f a) A) :
    ∃ dom cod, HasType [] f (Term.pi dom cod) := by
  cases hasType_app_empty_ctx_pi h with
  | intro dom rest =>
      cases rest with
      | intro cod hp =>
          exact Exists.intro dom (Exists.intro cod hp.left)

theorem hasType_app_empty_ctx_arg {f a A : Term}
    (h : HasType [] (Term.app f a) A) :
    ∃ dom, HasType [] a dom := by
  cases hasType_app_empty_ctx_pi h with
  | intro dom rest =>
      cases rest with
      | intro cod hp =>
          exact Exists.intro dom hp.right

theorem hasType_lam_ctx_components {Γ : Ctx} {dom body A : Term}
    (h : HasType Γ (Term.lam dom body) A) :
    ∃ cod,
      A = Term.pi dom cod ∧
        HasType Γ dom Term.sort ∧
          HasType ((shift 0 1 dom) :: Γ) body cod := by
  cases h with
  | lamRule Γ0 dom0 body0 cod hdom hbody =>
      exact Exists.intro cod
        (And.intro rfl (And.intro hdom hbody))

theorem hasType_lam_empty_ctx_pi {dom body A : Term}
    (h : HasType [] (Term.lam dom body) A) :
    ∃ cod,
      A = Term.pi dom cod ∧
        HasType [] dom Term.sort ∧
          HasType [shift 0 1 dom] body cod := by
  exact hasType_lam_ctx_components h

theorem hasType_lam_empty_ctx_type_pi {dom body A : Term}
    (h : HasType [] (Term.lam dom body) A) :
    ∃ cod, A = Term.pi dom cod := by
  cases hasType_lam_empty_ctx_pi h with
  | intro cod hcomponents =>
      exact Exists.intro cod hcomponents.left

theorem hasType_lam_empty_ctx_dom {dom body A : Term}
    (h : HasType [] (Term.lam dom body) A) :
    HasType [] dom Term.sort := by
  cases hasType_lam_empty_ctx_pi h with
  | intro cod hcomponents =>
      exact hcomponents.right.left

theorem hasType_lam_empty_ctx_body {dom body A : Term}
    (h : HasType [] (Term.lam dom body) A) :
    ∃ cod, HasType [shift 0 1 dom] body cod := by
  cases hasType_lam_empty_ctx_pi h with
  | intro cod hcomponents =>
      exact Exists.intro cod hcomponents.right.right

theorem hasType_pi_empty_ctx {dom cod A : Term}
    (h : HasType [] (Term.pi dom cod) A) :
    A = Term.sort := by
  exact hasType_pi_ctx_sort h

theorem hasType_pi_empty_ctx_components {dom cod A : Term}
    (h : HasType [] (Term.pi dom cod) A) :
    A = Term.sort ∧
      HasType [] dom Term.sort ∧
        HasType [shift 0 1 dom] cod Term.sort := by
  exact hasType_pi_ctx_components h

theorem hasType_pi_empty_ctx_dom {dom cod A : Term}
    (h : HasType [] (Term.pi dom cod) A) :
    HasType [] dom Term.sort := by
  exact (hasType_pi_empty_ctx_components h).right.left

theorem hasType_pi_empty_ctx_cod {dom cod A : Term}
    (h : HasType [] (Term.pi dom cod) A) :
    HasType [shift 0 1 dom] cod Term.sort := by
  exact (hasType_pi_empty_ctx_components h).right.right

end BEDC.MetaCIC
