import BEDC.MetaCIC.Typing.Core

namespace BEDC.MetaCIC

inductive ClosedBinderDomainTyping : Idx → Ctx → Term → Term → Prop
  | sortRule (d : Idx) (Γ : Ctx) :
      ClosedBinderDomainTyping d Γ Term.sort Term.sort
  | varRule (d : Idx) (Γ : Ctx) (i : Idx) (A : Term) :
      i < d →
      Ctx.lookup Γ i = some A →
      ClosedAt d A →
      ClosedBinderDomainTyping d Γ (Term.var i) A
  | piRule (d : Idx) (Γ : Ctx) (dom cod : Term) :
      ClosedBinderDomainTyping d Γ dom Term.sort →
      ClosedBinderDomainTyping (d + 1) ((shift 0 1 dom) :: Γ) cod Term.sort →
      ClosedBinderDomainTyping d Γ (Term.pi dom cod) Term.sort
  | lamRule (d : Idx) (Γ : Ctx) (dom body cod : Term) :
      ClosedBinderDomainTyping d Γ dom Term.sort →
      ClosedBinderDomainTyping (d + 1) ((shift 0 1 dom) :: Γ) body cod →
      ClosedBinderDomainTyping d Γ (Term.lam dom body) (Term.pi dom cod)
  | appRule (d : Idx) (Γ : Ctx) (f a dom cod : Term) :
      ClosedBinderDomainTyping d Γ f (Term.pi dom cod) →
      ClosedBinderDomainTyping d Γ a dom →
      ClosedAt d (substitute 0 a cod) →
      ClosedBinderDomainTyping d Γ (Term.app f a) (substitute 0 a cod)

def ClosedBinderDomainsSubstitutionSurface
    (Γ : Ctx) (t A : Term) : Prop :=
  ClosedBinderDomainTyping 0 Γ t A

theorem lookup_prefix_remove_closed_target
    (pref Γ : Ctx) (B : Term) {i : Idx} {A : Term}
    (hlt : i < pref.length)
    (hlookup : Ctx.lookup (pref ++ B :: Γ) i = some A) :
    Ctx.lookup (pref ++ Γ) i = some A := by
  induction pref generalizing i A with
  | nil =>
      exact False.elim (Nat.not_lt_zero i hlt)
  | cons head tail ih =>
      cases i with
      | zero =>
          exact hlookup
      | succ i =>
          change
            (match Ctx.lookup (tail ++ Γ) i with
            | some T => some (shift 0 1 T)
            | none => none) = some A
          change
            (match Ctx.lookup (tail ++ B :: Γ) i with
            | some T => some (shift 0 1 T)
            | none => none) = some A at hlookup
          cases htail : Ctx.lookup (tail ++ B :: Γ) i with
          | none =>
              rw [htail] at hlookup
              cases hlookup
          | some T =>
              rw [htail] at hlookup
              cases hlookup
              have hlt_tail : i < tail.length := by
                exact Nat.lt_of_succ_lt_succ hlt
              rw [ih hlt_tail htail]

theorem closedBinderDomainTyping_hasType
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    HasType Γ t A := by
  induction h with
  | sortRule d Γ =>
      exact HasType.sortRule Γ
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact HasType.varRule Γ i A hlookup
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      apply HasType.piRule
      · exact ihdom
      · exact ihcod
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      apply HasType.lamRule
      · exact ihdom
      · exact ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      apply HasType.appRule
      · exact ihf
      · exact iha

theorem closedBinderDomainTyping_term_closed
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    ClosedAt d t := by
  induction h with
  | sortRule d Γ =>
      exact ClosedAt.sortClosed
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact ClosedAt.varClosed hlt
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      exact ClosedAt.piClosed ihdom ihcod
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      exact ClosedAt.lamClosed ihdom ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      exact ClosedAt.appClosed ihf iha

theorem closedBinderDomainTyping_type_closed
    {d : Idx} {Γ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Γ t A) :
    ClosedAt d A := by
  induction h with
  | sortRule d Γ =>
      exact ClosedAt.sortClosed
  | varRule d Γ i A hlt hlookup hclosed_A =>
      exact hclosed_A
  | piRule d Γ dom cod hdom hcod ihdom ihcod =>
      exact ClosedAt.sortClosed
  | lamRule d Γ dom body cod hdom hbody ihdom ihbody =>
      exact ClosedAt.piClosed
        (closedBinderDomainTyping_term_closed hdom)
        ihbody
  | appRule d Γ f a dom cod hf ha hclosed_result ihf iha =>
      exact hclosed_result

theorem closedBinderDomainTyping_remove_prefix
    {d : Idx} {Δ : Ctx} {t A : Term}
    (h : ClosedBinderDomainTyping d Δ t A) :
    ∀ (pref Γ : Ctx) (B : Term),
      Δ = pref ++ B :: Γ →
      d = pref.length →
      ClosedBinderDomainTyping d (pref ++ Γ) t A := by
  induction h with
  | sortRule d Δ =>
      intro pref Γ B hctx hd
      exact ClosedBinderDomainTyping.sortRule d (pref ++ Γ)
  | varRule d Δ i A hlt hlookup hclosed_A =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.varRule
      · exact hlt
      · rw [hd] at hlt
        exact lookup_prefix_remove_closed_target pref Γ B hlt (by
          rw [← hctx]
          exact hlookup)
      · exact hclosed_A
  | piRule d Δ dom cod hdom hcod ihdom ihcod =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.piRule
      · exact ihdom pref Γ B hctx hd
      · exact ihcod
          ((shift 0 1 dom) :: pref)
          Γ
          B
          (by
            rw [hctx]
            rfl)
          (by
            rw [hd]
            rfl)
  | lamRule d Δ dom body cod hdom hbody ihdom ihbody =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.lamRule
      · exact ihdom pref Γ B hctx hd
      · exact ihbody
          ((shift 0 1 dom) :: pref)
          Γ
          B
          (by
            rw [hctx]
            rfl)
          (by
            rw [hd]
            rfl)
  | appRule d Δ f a dom cod hf ha hclosed_result ihf iha =>
      intro pref Γ B hctx hd
      apply ClosedBinderDomainTyping.appRule
      · exact ihf pref Γ B hctx hd
      · exact iha pref Γ B hctx hd
      · exact hclosed_result

theorem closedBinderDomainTyping_remove_target
    {Γ : Ctx} {B t A : Term}
    (h : ClosedBinderDomainsSubstitutionSurface (B :: Γ) t A) :
    ClosedBinderDomainsSubstitutionSurface Γ t A := by
  exact closedBinderDomainTyping_remove_prefix h [] Γ B rfl rfl

theorem substitute_preserves_typing_closed_binder_domains
    {Γ : Ctx} {t s A B : Term}
    (_hclosed_B : ClosedAt 0 B)
    (_hclosed_s : ClosedAt 0 s)
    (hclosed_all_binder_doms :
      ClosedBinderDomainsSubstitutionSurface (B :: Γ) t A)
    (_ht : HasType (B :: Γ) t A)
    (_hs : HasType Γ s B) :
    HasType Γ (substitute 0 s t) (substitute 0 s A) := by
  have hremoved :
      ClosedBinderDomainsSubstitutionSurface Γ t A := by
    exact closedBinderDomainTyping_remove_target hclosed_all_binder_doms
  have htyped : HasType Γ t A := by
    exact closedBinderDomainTyping_hasType hremoved
  have hclosed_t : ClosedAt 0 t := by
    exact closedBinderDomainTyping_term_closed hclosed_all_binder_doms
  have hclosed_A : ClosedAt 0 A := by
    exact closedBinderDomainTyping_type_closed hclosed_all_binder_doms
  rw [substitute_closed 0 s t hclosed_t]
  rw [substitute_closed 0 s A hclosed_A]
  exact htyped

end BEDC.MetaCIC
