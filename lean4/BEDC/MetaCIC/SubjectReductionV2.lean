import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.TypingV2

namespace BEDC.MetaCIC.V2

def BetaSubstitutionPreservationV2 : Prop :=
  ∀ {Γ : Ctx} {dom body arg cod : Term},
    HasTypeV2 ((shift 0 1 dom) :: Γ) body cod →
    HasTypeV2 Γ arg dom →
    HasTypeV2 Γ (substitute 0 arg body) (substitute 0 arg cod)

theorem betaSubstitutionPreservationV2_sort_var
    {Γ : Ctx} {dom body arg cod : Term}
    (hbody : HasTypeV2 ((shift 0 1 dom) :: Γ) body cod)
    (harg : HasTypeV2 Γ arg dom)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasTypeV2 Γ (substitute 0 arg body) (substitute 0 arg cod) := by
  cases hbody with
  | sortRule Δ =>
      exact HasTypeV2.sortRule Γ
  | varRule Δ i _ hlookup =>
      cases i with
      | zero =>
          change some (shift 0 1 dom) = some cod at hlookup
          cases hlookup
          rw [substitute_var_zero]
          rw [substitute_shift_at_eq]
          exact harg
      | succ i =>
          rw [lookup_cons_succ] at hlookup
          cases hlook : Ctx.lookup Γ i with
          | none =>
              rw [hlook] at hlookup
              cases hlookup
          | some T =>
              rw [hlook] at hlookup
              cases hlookup
              rw [substitute_var_succ_zero]
              rw [substitute_shift_at_eq]
              exact HasTypeV2.varRule Γ i T hlook
  | piRule Δ piDom piCod hdom hcod =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | lamRule Δ lamDom lamBody lamCod hdom hbody =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi
  | appRule Δ f a appDom appCod hf ha =>
      cases hshape with
      | inl hsort => cases hsort
      | inr hvar =>
          cases hvar with
          | intro i hi => cases hi

theorem betaSubstitutionPreservationV2_depth_one_sort_var
    {Γ : Ctx} {dom head arg t A : Term}
    (hclosed_dom : ClosedAt 0 dom)
    (hclosed_arg : ClosedAt 0 arg)
    (hclosed_head : ClosedAt 0 head)
    (hshape_arg : arg = Term.sort ∨ ∃ i : Idx, arg = Term.var i)
    (hshape_t : t = Term.sort ∨ ∃ i : Idx, t = Term.var i)
    (ht :
      HasTypeV2 ((shift 0 1 head) :: (shift 0 1 dom) :: Γ) t A)
    (harg : HasTypeV2 Γ arg dom) :
    HasTypeV2 ((shift 0 1 head) :: Γ)
      (substitute 1 (shift 0 1 arg) t)
      (substitute 1 (shift 0 1 arg) A) := by
  have hdom_eq : shift 0 1 dom = dom := by
    exact shift_closed 0 dom hclosed_dom
  have ht_dom :
      HasTypeV2 ((shift 0 1 head) :: dom :: Γ) t A := by
    rw [← hdom_eq]
    exact ht
  have hclosed_head_after : ClosedAt 0 (shift 0 1 head) := by
    rw [shift_closed 0 head hclosed_head]
    exact hclosed_head
  exact substitute_preserves_typing_V2_depth1_sort_var_with_weaken
    hclosed_dom
    hclosed_arg
    hclosed_head_after
    ht_dom
    (hasTypeV2_shift_weaken_sort_var
      (C := shift 0 1 head) harg hshape_arg)
    hshape_t

theorem betaSubstitutionPreservationV2_pi_body
    {Γ : Ctx} {dom bodyDom bodyCod arg cod : Term}
    (hclosed_dom : ClosedAt 0 dom)
    (hclosed_arg : ClosedAt 0 arg)
    (hclosed_bodyDom : ClosedAt 0 bodyDom)
    (hshape_arg : arg = Term.sort ∨ ∃ i : Idx, arg = Term.var i)
    (hshape_bodyDom :
      bodyDom = Term.sort ∨ ∃ i : Idx, bodyDom = Term.var i)
    (hshape_bodyCod :
      bodyCod = Term.sort ∨ ∃ i : Idx, bodyCod = Term.var i)
    (hbody :
      HasTypeV2 ((shift 0 1 dom) :: Γ)
        (Term.pi bodyDom bodyCod) cod)
    (harg : HasTypeV2 Γ arg dom) :
    HasTypeV2 Γ
      (substitute 0 arg (Term.pi bodyDom bodyCod))
      (substitute 0 arg cod) := by
  cases hbody with
  | piRule Δ _ _ hdom hcod =>
      have hdom_sub :
          HasTypeV2 Γ (substitute 0 arg bodyDom) Term.sort := by
        exact betaSubstitutionPreservationV2_sort_var
          hdom harg hshape_bodyDom
      have hdom_clean : HasTypeV2 Γ bodyDom Term.sort := by
        rw [← substitute_closed 0 arg bodyDom hclosed_bodyDom]
        exact hdom_sub
      change HasTypeV2 Γ
        (Term.pi (substitute 0 arg bodyDom)
          (substitute 1 (shift 0 1 arg) bodyCod))
        Term.sort
      rw [substitute_closed 0 arg bodyDom hclosed_bodyDom]
      apply HasTypeV2.piRule
      · exact hdom_clean
      · exact betaSubstitutionPreservationV2_depth_one_sort_var
          hclosed_dom
          hclosed_arg
          hclosed_bodyDom
          hshape_arg
          hshape_bodyCod
          hcod
          harg

theorem betaSubstitutionPreservationV2_lam_body
    {Γ : Ctx} {dom lamDom lamBody arg cod : Term}
    (hclosed_dom : ClosedAt 0 dom)
    (hclosed_arg : ClosedAt 0 arg)
    (hclosed_lamDom : ClosedAt 0 lamDom)
    (hshape_arg : arg = Term.sort ∨ ∃ i : Idx, arg = Term.var i)
    (hshape_lamDom :
      lamDom = Term.sort ∨ ∃ i : Idx, lamDom = Term.var i)
    (hshape_lamBody :
      lamBody = Term.sort ∨ ∃ i : Idx, lamBody = Term.var i)
    (hbody :
      HasTypeV2 ((shift 0 1 dom) :: Γ)
        (Term.lam lamDom lamBody) cod)
    (harg : HasTypeV2 Γ arg dom) :
    HasTypeV2 Γ
      (substitute 0 arg (Term.lam lamDom lamBody))
      (substitute 0 arg cod) := by
  cases hbody with
  | lamRule Δ _ _ codBody hdom hbody =>
      have hdom_sub :
          HasTypeV2 Γ (substitute 0 arg lamDom) Term.sort := by
        exact betaSubstitutionPreservationV2_sort_var
          hdom harg hshape_lamDom
      have hdom_clean : HasTypeV2 Γ lamDom Term.sort := by
        rw [← substitute_closed 0 arg lamDom hclosed_lamDom]
        exact hdom_sub
      change HasTypeV2 Γ
        (Term.lam (substitute 0 arg lamDom)
          (substitute 1 (shift 0 1 arg) lamBody))
        (Term.pi (substitute 0 arg lamDom)
          (substitute 1 (shift 0 1 arg) codBody))
      rw [substitute_closed 0 arg lamDom hclosed_lamDom]
      apply HasTypeV2.lamRule
      · exact hdom_clean
      · exact betaSubstitutionPreservationV2_depth_one_sort_var
          hclosed_dom
          hclosed_arg
          hclosed_lamDom
          hshape_arg
          hshape_lamBody
          hbody
          harg

theorem betaSubstitutionPreservationV2_app_body
    {Γ : Ctx} {dom f a arg cod : Term}
    (hclosed_dom : ClosedAt 0 dom)
    (hclosed_arg : ClosedAt 0 arg)
    (hshape_f : f = Term.sort ∨ ∃ i : Idx, f = Term.var i)
    (hshape_a : a = Term.sort ∨ ∃ i : Idx, a = Term.var i)
    (hshape_appCod :
      ∀ {appCod : Term},
        cod = substitute 0 a appCod →
        appCod = Term.sort ∨ ∃ i : Idx, appCod = Term.var i)
    (hbody :
      HasTypeV2 ((shift 0 1 dom) :: Γ)
        (Term.app f a) cod)
    (harg : HasTypeV2 Γ arg dom) :
    HasTypeV2 Γ
      (substitute 0 arg (Term.app f a))
      (substitute 0 arg cod) := by
  cases hbody with
  | appRule Δ f a appDom appCod hf ha =>
      have hf_sub :
          HasTypeV2 Γ
            (substitute 0 arg f)
            (Term.pi (substitute 0 arg appDom)
              (substitute 1 (shift 0 1 arg) appCod)) := by
        exact betaSubstitutionPreservationV2_sort_var hf harg hshape_f
      have ha_sub :
          HasTypeV2 Γ
            (substitute 0 arg a)
            (substitute 0 arg appDom) := by
        exact betaSubstitutionPreservationV2_sort_var ha harg hshape_a
      have hcod_sub :
          substitute 0 (substitute 0 arg a)
              (substitute 1 (shift 0 1 arg) appCod) =
            substitute 0 arg (substitute 0 a appCod) := by
        rw [shift_closed 0 arg hclosed_arg]
        cases hshape_appCod rfl with
        | inl hsort =>
            cases hsort
            exact Eq.symm
              (substitute_substitute_zero_zero_closed_sort
                arg a hclosed_arg)
        | inr hvar =>
            cases hvar with
            | intro i hi =>
                cases hi
                exact Eq.symm
                  (substitute_substitute_zero_zero_closed_var
                    arg a i hclosed_arg)
      exact substitute_preserves_typing_V2_app_if_subderivations
        hclosed_dom
        hclosed_arg
        hf_sub
        ha_sub
        harg
        hcod_sub

theorem subject_reduction_V2_beta_sort_var
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasTypeV2 Γ (Term.app (Term.lam dom body) arg) A)
    (hshape : body = Term.sort ∨ ∃ i : Idx, body = Term.var i) :
    HasTypeV2 Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact betaSubstitutionPreservationV2_sort_var hbody ha hshape

theorem subject_reduction_V2_beta
    (hsubst : BetaSubstitutionPreservationV2)
    {Γ : Ctx} {dom body arg A : Term}
    (ht : HasTypeV2 Γ (Term.app (Term.lam dom body) arg) A) :
    HasTypeV2 Γ (substitute 0 arg body) A := by
  cases ht with
  | appRule Γ f a appDom cod hf ha =>
      cases hf with
      | lamRule Γ lamDom lamBody lamCod hdom hbody =>
          exact hsubst hbody ha

theorem subject_reduction_V2_congApp1
    {Γ : Ctx} {f f' a A : Term}
    (ht : HasTypeV2 Γ (Term.app f a) A)
    (_hb : BetaStep f f')
    (ih : ∀ {B : Term}, HasTypeV2 Γ f B → HasTypeV2 Γ f' B) :
    HasTypeV2 Γ (Term.app f' a) A := by
  cases ht with
  | appRule Γ f a dom cod hf ha =>
      exact HasTypeV2.appRule Γ f' a dom cod (ih hf) ha

theorem subject_reduction_V2_congApp2
    {Γ : Ctx} {f a a' A : Term}
    (ht : HasTypeV2 Γ (Term.app f a) A)
    (_hb : BetaStep a a')
    (ih : ∀ {B : Term}, HasTypeV2 Γ a B → HasTypeV2 Γ a' B) :
    ∃ A' : Term, HasTypeV2 Γ (Term.app f a') A' := by
  cases ht with
  | appRule Γ f a dom cod hf ha =>
      exact ⟨substitute 0 a' cod, HasTypeV2.appRule Γ f a' dom cod hf (ih ha)⟩

theorem subject_reduction_V2_congLam
    {Γ : Ctx} {d b b' A : Term}
    (ht : HasTypeV2 Γ (Term.lam d b) A)
    (_hb : BetaStep b b')
    (ih : ∀ {B : Term},
      HasTypeV2 ((shift 0 1 d) :: Γ) b B →
      HasTypeV2 ((shift 0 1 d) :: Γ) b' B) :
    HasTypeV2 Γ (Term.lam d b') A := by
  cases ht with
  | lamRule Γ dom body cod hdom hbody =>
      exact HasTypeV2.lamRule Γ d b' cod hdom (ih hbody)

theorem subject_reduction_V2_congPi
    {Γ : Ctx} {dom cod cod' A : Term}
    (ht : HasTypeV2 Γ (Term.pi dom cod) A)
    (_hb : BetaStep cod cod')
    (ih :
      HasTypeV2 ((shift 0 1 dom) :: Γ) cod Term.sort →
      HasTypeV2 ((shift 0 1 dom) :: Γ) cod' Term.sort) :
    HasTypeV2 Γ (Term.pi dom cod') A := by
  cases ht with
  | piRule Γ dom cod hdom hcod =>
      exact HasTypeV2.piRule Γ dom cod' hdom (ih hcod)

end BEDC.MetaCIC.V2
