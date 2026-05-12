import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

namespace Term

def eq : Term → Term → Bool
  | Term.sort, Term.sort => true
  | Term.sort, Term.var _ => false
  | Term.sort, Term.app _ _ => false
  | Term.sort, Term.lam _ _ => false
  | Term.sort, Term.pi _ _ => false
  | Term.var _, Term.sort => false
  | Term.var i, Term.var j => Nat.beq i j
  | Term.var _, Term.app _ _ => false
  | Term.var _, Term.lam _ _ => false
  | Term.var _, Term.pi _ _ => false
  | Term.pi _ _, Term.sort => false
  | Term.pi _ _, Term.var _ => false
  | Term.pi _ _, Term.app _ _ => false
  | Term.pi _ _, Term.lam _ _ => false
  | Term.pi d1 c1, Term.pi d2 c2 => Term.eq d1 d2 && Term.eq c1 c2
  | Term.lam _ _, Term.sort => false
  | Term.lam _ _, Term.var _ => false
  | Term.lam _ _, Term.app _ _ => false
  | Term.lam d1 b1, Term.lam d2 b2 => Term.eq d1 d2 && Term.eq b1 b2
  | Term.lam _ _, Term.pi _ _ => false
  | Term.app _ _, Term.sort => false
  | Term.app _ _, Term.var _ => false
  | Term.app f1 a1, Term.app f2 a2 => Term.eq f1 f2 && Term.eq a1 a2
  | Term.app _ _, Term.lam _ _ => false
  | Term.app _ _, Term.pi _ _ => false

theorem eq_refl (t : Term) : Term.eq t t = true := by
  induction t with
  | var i =>
      unfold Term.eq
      induction i with
      | zero => rfl
      | succ i ih =>
          change Nat.beq (i + 1) (i + 1) = true
          rw [nat_beq_add_one_add_one]
          exact ih
  | app f a ihf iha =>
      unfold Term.eq
      rw [ihf, iha]
      rfl
  | lam dom body ihdom ihbody =>
      unfold Term.eq
      rw [ihdom, ihbody]
      rfl
  | pi dom cod ihdom ihcod =>
      unfold Term.eq
      rw [ihdom, ihcod]
      rfl
  | sort =>
      rfl

theorem nat_eq_of_beq_true (i j : Nat) : Nat.beq i j = true → i = j := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero =>
          intro _
          rfl
      | succ j =>
          intro h
          cases h
  | succ i ih =>
      cases j with
      | zero =>
          intro h
          cases h
      | succ j =>
          intro h
          rw [nat_beq_add_one_add_one] at h
          exact congrArg Nat.succ (ih j h)

theorem beq_true_of_nat_eq {i j : Nat} : i = j → Nat.beq i j = true := by
  intro h
  cases h
  induction i with
  | zero => rfl
  | succ i ih =>
      change Nat.beq (i + 1) (i + 1) = true
      rw [nat_beq_add_one_add_one]
      exact ih

theorem eq_true_to_eq (t u : Term) : Term.eq t u = true → t = u := by
  induction t generalizing u with
  | var i =>
      cases u with
      | var j =>
          intro h
          unfold Term.eq at h
          exact congrArg Term.var (nat_eq_of_beq_true i j h)
      | app f a =>
          intro h
          cases h
      | lam dom body =>
          intro h
          cases h
      | pi dom cod =>
          intro h
          cases h
      | sort =>
          intro h
          cases h
  | app f a ihf iha =>
      cases u with
      | var i =>
          intro h
          cases h
      | app g b =>
          intro h
          unfold Term.eq at h
          cases hf : Term.eq f g with
          | false =>
              rw [hf] at h
              cases h
          | true =>
              rw [hf] at h
              have hfg : f = g := ihf g hf
              have hab : a = b := iha b h
              cases hfg
              cases hab
              rfl
      | lam dom body =>
          intro h
          cases h
      | pi dom cod =>
          intro h
          cases h
      | sort =>
          intro h
          cases h
  | lam dom body ihdom ihbody =>
      cases u with
      | var i =>
          intro h
          cases h
      | app f a =>
          intro h
          cases h
      | lam dom' body' =>
          intro h
          unfold Term.eq at h
          cases hd : Term.eq dom dom' with
          | false =>
              rw [hd] at h
              cases h
          | true =>
              rw [hd] at h
              have hdom : dom = dom' := ihdom dom' hd
              have hbody : body = body' := ihbody body' h
              cases hdom
              cases hbody
              rfl
      | pi dom' cod' =>
          intro h
          cases h
      | sort =>
          intro h
          cases h
  | pi dom cod ihdom ihcod =>
      cases u with
      | var i =>
          intro h
          cases h
      | app f a =>
          intro h
          cases h
      | lam dom' body' =>
          intro h
          cases h
      | pi dom' cod' =>
          intro h
          unfold Term.eq at h
          cases hd : Term.eq dom dom' with
          | false =>
              rw [hd] at h
              cases h
          | true =>
              rw [hd] at h
              have hdom : dom = dom' := ihdom dom' hd
              have hcod : cod = cod' := ihcod cod' h
              cases hdom
              cases hcod
              rfl
      | sort =>
          intro h
          cases h
  | sort =>
      cases u with
      | var i =>
          intro h
          cases h
      | app f a =>
          intro h
          cases h
      | lam dom body =>
          intro h
          cases h
      | pi dom cod =>
          intro h
          cases h
      | sort =>
          intro _
          rfl

theorem eq_eq_to_true (t u : Term) : t = u → Term.eq t u = true := by
  intro h
  cases h
  exact eq_refl t

theorem eq_correct (t u : Term) : Term.eq t u = true ↔ t = u := by
  constructor
  · exact eq_true_to_eq t u
  · exact eq_eq_to_true t u

theorem eq_false_of_ne {t u : Term} : (t = u → False) → Term.eq t u = false := by
  intro hne
  cases h : Term.eq t u with
  | false => rfl
  | true =>
      have heq : t = u := eq_true_to_eq t u h
      exact False.elim (hne heq)

end Term

def checkSameTerm (t u : Term) : Option Unit :=
  match Term.eq t u with
  | true => some ()
  | false => none

def inferType : Ctx → Term → Option Term
  | _, Term.sort => some Term.sort
  | Γ, Term.var i => Γ.lookup i
  | Γ, Term.pi dom cod =>
      match inferType Γ dom with
      | some Term.sort =>
          match inferType ((shift 0 1 dom) :: Γ) cod with
          | some Term.sort => some Term.sort
          | some (Term.var _) => none
          | some (Term.app _ _) => none
          | some (Term.lam _ _) => none
          | some (Term.pi _ _) => none
          | none => none
      | some (Term.var _) => none
      | some (Term.app _ _) => none
      | some (Term.lam _ _) => none
      | some (Term.pi _ _) => none
      | none => none
  | Γ, Term.lam dom body =>
      match inferType Γ dom with
      | some Term.sort =>
          match inferType ((shift 0 1 dom) :: Γ) body with
          | some cod => some (Term.pi dom cod)
          | none => none
      | some (Term.var _) => none
      | some (Term.app _ _) => none
      | some (Term.lam _ _) => none
      | some (Term.pi _ _) => none
      | none => none
  | Γ, Term.app f a =>
      match inferType Γ f with
      | some (Term.pi dom cod) =>
          match inferType Γ a with
          | some A =>
              match checkSameTerm A dom with
              | some () => some (substitute 0 a cod)
              | none => none
          | none => none
      | some Term.sort => none
      | some (Term.var _) => none
      | some (Term.app _ _) => none
      | some (Term.lam _ _) => none
      | none => none

def inferTypeClosed : Term → Option Term :=
  inferType []

theorem checkSameTerm_sound {t u : Term} :
    checkSameTerm t u = some () → t = u := by
  unfold checkSameTerm
  cases h : Term.eq t u with
  | false =>
      intro hcheck
      cases hcheck
  | true =>
      intro _
      exact Term.eq_true_to_eq t u h

theorem checkSameTerm_complete {t u : Term} :
    t = u → checkSameTerm t u = some () := by
  intro h
  unfold checkSameTerm
  rw [Term.eq_eq_to_true t u h]

theorem inferType_sound (Γ : Ctx) (t A : Term)
    (h : inferType Γ t = some A) :
    HasType Γ t A := by
  induction t generalizing Γ A with
  | sort =>
      unfold inferType at h
      cases h
      exact HasType.sortRule Γ
  | var i =>
      unfold inferType at h
      exact HasType.varRule Γ i A h
  | pi dom cod ihdom ihcod =>
      unfold inferType at h
      cases hdom : inferType Γ dom with
      | none =>
          rw [hdom] at h
          cases h
      | some domTy =>
          rw [hdom] at h
          cases domTy with
          | sort =>
              cases hcod : inferType ((shift 0 1 dom) :: Γ) cod with
              | none =>
                  rw [hcod] at h
                  cases h
              | some codTy =>
                  rw [hcod] at h
                  cases codTy with
                  | sort =>
                      cases h
                      exact HasType.piRule Γ dom cod
                        (ihdom Γ Term.sort hdom)
                        (ihcod ((shift 0 1 dom) :: Γ) Term.sort hcod)
                  | var i =>
                      cases h
                  | app f a =>
                      cases h
                  | lam d b =>
                      cases h
                  | pi d c =>
                      cases h
          | var i =>
              cases h
          | app f a =>
              cases h
          | lam d b =>
              cases h
          | pi d c =>
              cases h
  | lam dom body ihdom ihbody =>
      unfold inferType at h
      cases hdom : inferType Γ dom with
      | none =>
          rw [hdom] at h
          cases h
      | some domTy =>
          rw [hdom] at h
          cases domTy with
          | sort =>
              cases hbody : inferType ((shift 0 1 dom) :: Γ) body with
              | none =>
                  rw [hbody] at h
                  cases h
              | some cod =>
                  rw [hbody] at h
                  cases h
                  exact HasType.lamRule Γ dom body cod
                    (ihdom Γ Term.sort hdom)
                    (ihbody ((shift 0 1 dom) :: Γ) cod hbody)
          | var i =>
              cases h
          | app f a =>
              cases h
          | lam d b =>
              cases h
          | pi d c =>
              cases h
  | app f a ihf iha =>
      unfold inferType at h
      cases hf : inferType Γ f with
      | none =>
          rw [hf] at h
          cases h
      | some fTy =>
          rw [hf] at h
          cases fTy with
          | pi dom cod =>
              cases ha : inferType Γ a with
              | none =>
                  rw [ha] at h
                  cases h
              | some A0 =>
                  rw [ha] at h
                  change
                    (match checkSameTerm A0 dom with
                    | some () => some (substitute 0 a cod)
                    | none => none) = some A at h
                  cases hcheck : checkSameTerm A0 dom with
                  | none =>
                      rw [hcheck] at h
                      cases h
                  | some unitValue =>
                      cases unitValue
                      rw [hcheck] at h
                      have hA : A0 = dom := checkSameTerm_sound hcheck
                      cases hA
                      cases h
                      exact HasType.appRule Γ f a dom cod
                        (ihf Γ (Term.pi dom cod) hf)
                        (iha Γ dom ha)
          | sort =>
              cases h
          | var i =>
              cases h
          | app g b =>
              cases h
          | lam d b =>
              cases h

theorem inferTypeClosed_sound (t A : Term)
    (h : inferTypeClosed t = some A) (_hclosed : ClosedAt 0 t) :
    HasType [] t A :=
  inferType_sound [] t A h

theorem inferType_complete (Γ : Ctx) (t A : Term)
    (h : HasType Γ t A) :
    inferType Γ t = some A := by
  induction h with
  | sortRule Γ =>
      rfl
  | varRule Γ i A hlookup =>
      unfold inferType
      exact hlookup
  | piRule Γ dom cod hdom hcod ihdom ihcod =>
      unfold inferType
      rw [ihdom, ihcod]
  | lamRule Γ dom body cod hdom hbody ihdom ihbody =>
      unfold inferType
      rw [ihdom, ihbody]
  | appRule Γ f a dom cod hf ha ihf iha =>
      unfold inferType
      rw [ihf, iha]
      change
        (match checkSameTerm dom dom with
        | some () => some (substitute 0 a cod)
        | none => none) = some (substitute 0 a cod)
      rw [checkSameTerm_complete rfl]

theorem inferTypeClosed_complete (t A : Term)
    (h : HasType [] t A) :
    inferTypeClosed t = some A :=
  inferType_complete [] t A h

theorem inferTypeClosed_complete_sort :
    inferTypeClosed Term.sort = some Term.sort :=
  rfl

theorem inferTypeClosed_complete_pi {dom cod : Term}
    (hT : HasType [] (Term.pi dom cod) Term.sort) :
    inferTypeClosed (Term.pi dom cod) = some Term.sort :=
  inferTypeClosed_complete (Term.pi dom cod) Term.sort hT

theorem inferTypeClosed_complete_lam {dom body cod : Term}
    (hT : HasType [] (Term.lam dom body) (Term.pi dom cod)) :
    inferTypeClosed (Term.lam dom body) = some (Term.pi dom cod) :=
  inferTypeClosed_complete (Term.lam dom body) (Term.pi dom cod) hT

theorem inferTypeClosed_complete_app {f a dom cod : Term}
    (_hT : HasType [] (Term.app f a) (substitute 0 a cod))
    (hf : HasType [] f (Term.pi dom cod))
    (ha : HasType [] a dom) :
    inferTypeClosed (Term.app f a) = some (substitute 0 a cod) := by
  exact inferType_complete [] (Term.app f a) (substitute 0 a cod)
    (HasType.appRule [] f a dom cod hf ha)

theorem inferTypeClosed_var_empty_none (i : Idx) :
    inferTypeClosed (Term.var i) = none :=
  rfl

end BEDC.MetaCIC
