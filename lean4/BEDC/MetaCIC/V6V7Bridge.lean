import BEDC.MetaCIC.TypingV2

namespace BEDC.MetaCIC

inductive HasTypeClosedDomains : {Γ : Ctx} → {t A : Term} → HasType Γ t A → Prop
  | sortRule (Γ : Ctx) :
      HasTypeClosedDomains (HasType.sortRule Γ)
  | varRule (Γ : Ctx) (i : Idx) (A : Term) (hlook : Γ.lookup i = some A) :
      HasTypeClosedDomains (HasType.varRule Γ i A hlook)
  | piRule {Γ : Ctx} {dom cod : Term}
      {hdom : HasType Γ dom Term.sort}
      {hcod : HasType (dom :: Γ) cod Term.sort} :
      ClosedAt 0 dom →
      HasTypeClosedDomains hdom →
      HasTypeClosedDomains hcod →
      HasTypeClosedDomains (HasType.piRule Γ dom cod hdom hcod)
  | lamRule {Γ : Ctx} {dom body cod : Term}
      {hdom : HasType Γ dom Term.sort}
      {hbody : HasType (dom :: Γ) body cod} :
      ClosedAt 0 dom →
      HasTypeClosedDomains hdom →
      HasTypeClosedDomains hbody →
      HasTypeClosedDomains (HasType.lamRule Γ dom body cod hdom hbody)
  | appRule {Γ : Ctx} {f a dom cod : Term}
      {hf : HasType Γ f (Term.pi dom cod)}
      {ha : HasType Γ a dom} :
      HasTypeClosedDomains hf →
      HasTypeClosedDomains ha →
      HasTypeClosedDomains (HasType.appRule Γ f a dom cod hf ha)

inductive HasTypeV2ClosedDomains :
    {Γ : Ctx} → {t A : Term} → V2.HasTypeV2 Γ t A → Prop
  | sortRule (Γ : Ctx) :
      HasTypeV2ClosedDomains (V2.HasTypeV2.sortRule Γ)
  | varRule (Γ : Ctx) (i : Idx) (A : Term) (hlook : Γ.lookup i = some A) :
      HasTypeV2ClosedDomains (V2.HasTypeV2.varRule Γ i A hlook)
  | piRule {Γ : Ctx} {dom cod : Term}
      {hdom : V2.HasTypeV2 Γ dom Term.sort}
      {hcod : V2.HasTypeV2 ((shift 0 1 dom) :: Γ) cod Term.sort} :
      ClosedAt 0 dom →
      HasTypeV2ClosedDomains hdom →
      HasTypeV2ClosedDomains hcod →
      HasTypeV2ClosedDomains (V2.HasTypeV2.piRule Γ dom cod hdom hcod)
  | lamRule {Γ : Ctx} {dom body cod : Term}
      {hdom : V2.HasTypeV2 Γ dom Term.sort}
      {hbody : V2.HasTypeV2 ((shift 0 1 dom) :: Γ) body cod} :
      ClosedAt 0 dom →
      HasTypeV2ClosedDomains hdom →
      HasTypeV2ClosedDomains hbody →
      HasTypeV2ClosedDomains (V2.HasTypeV2.lamRule Γ dom body cod hdom hbody)
  | appRule {Γ : Ctx} {f a dom cod : Term}
      {hf : V2.HasTypeV2 Γ f (Term.pi dom cod)}
      {ha : V2.HasTypeV2 Γ a dom} :
      HasTypeV2ClosedDomains hf →
      HasTypeV2ClosedDomains ha →
      HasTypeV2ClosedDomains (V2.HasTypeV2.appRule Γ f a dom cod hf ha)

theorem shift_closed_term_only {t : Term} :
    ClosedAt 0 t → shift 0 1 t = t := by
  intro hclosed
  exact shift_closed 0 t hclosed

theorem hasType_V6_to_V2_closedDomains
    {Γ : Ctx} {t A : Term}
    (ht : HasType Γ t A)
    (hclosed : HasTypeClosedDomains ht) :
    V2.HasTypeV2 Γ t A := by
  induction hclosed with
  | sortRule Γ =>
      exact V2.HasTypeV2.sortRule Γ
  | varRule Γ i A hlook =>
      exact V2.HasTypeV2.varRule Γ i A hlook
  | piRule hclosed_dom _ _ ihdom ihcod =>
      apply V2.HasTypeV2.piRule
      · exact ihdom
      · rw [shift_closed 0 _ hclosed_dom]
        exact ihcod
  | lamRule hclosed_dom _ _ ihdom ihbody =>
      apply V2.HasTypeV2.lamRule
      · exact ihdom
      · rw [shift_closed 0 _ hclosed_dom]
        exact ihbody
  | appRule _ _ ihf iha =>
      exact V2.HasTypeV2.appRule _ _ _ _ _ ihf iha

theorem hasType_V2_to_V6_closedDomains
    {Γ : Ctx} {t A : Term}
    (ht : V2.HasTypeV2 Γ t A)
    (hclosed : HasTypeV2ClosedDomains ht) :
    HasType Γ t A := by
  induction hclosed with
  | sortRule Γ =>
      exact HasType.sortRule Γ
  | varRule Γ i A hlook =>
      exact HasType.varRule Γ i A hlook
  | piRule hclosed_dom _ _ ihdom ihcod =>
      apply HasType.piRule
      · exact ihdom
      · rw [← shift_closed 0 _ hclosed_dom]
        exact ihcod
  | lamRule hclosed_dom _ _ ihdom ihbody =>
      apply HasType.lamRule
      · exact ihdom
      · rw [← shift_closed 0 _ hclosed_dom]
        exact ihbody
  | appRule _ _ ihf iha =>
      exact HasType.appRule _ _ _ _ _ ihf iha

end BEDC.MetaCIC
