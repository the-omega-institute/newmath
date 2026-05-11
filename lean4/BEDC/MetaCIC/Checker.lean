import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- 比较两个 Term 是否结构相等。 -/
def Term.beq : Term → Term → Bool
  | Term.var i, Term.var j => decide (i = j)
  | Term.app f a, Term.app f' a' => Term.beq f f' && Term.beq a a'
  | Term.lam d b, Term.lam d' b' => Term.beq d d' && Term.beq b b'
  | Term.pi d c, Term.pi d' c' => Term.beq d d' && Term.beq c c'
  | Term.sort, Term.sort => true
  | _, _ => false

/-- `Term.beq` 为真时两个项相等。 -/
theorem Term.beq_eq {x y : Term} (h : Term.beq x y = true) : x = y := by
  induction x generalizing y with
  | var i =>
      cases y with
      | var j =>
          simp [Term.beq] at h
          rw [h]
      | app f a => simp [Term.beq] at h
      | lam d b => simp [Term.beq] at h
      | pi d c => simp [Term.beq] at h
      | sort => simp [Term.beq] at h
  | app f a ihF ihA =>
      cases y with
      | var j => simp [Term.beq] at h
      | app f' a' =>
          simp [Term.beq] at h
          cases ihF h.left
          cases ihA h.right
          rfl
      | lam d b => simp [Term.beq] at h
      | pi d c => simp [Term.beq] at h
      | sort => simp [Term.beq] at h
  | lam d b ihD ihB =>
      cases y with
      | var j => simp [Term.beq] at h
      | app f a => simp [Term.beq] at h
      | lam d' b' =>
          simp [Term.beq] at h
          cases ihD h.left
          cases ihB h.right
          rfl
      | pi d' c' => simp [Term.beq] at h
      | sort => simp [Term.beq] at h
  | pi d c ihD ihC =>
      cases y with
      | var j => simp [Term.beq] at h
      | app f a => simp [Term.beq] at h
      | lam d' b => simp [Term.beq] at h
      | pi d' c' =>
          simp [Term.beq] at h
          cases ihD h.left
          cases ihC h.right
          rfl
      | sort => simp [Term.beq] at h
  | sort =>
      cases y with
      | var j => simp [Term.beq] at h
      | app f a => simp [Term.beq] at h
      | lam d b => simp [Term.beq] at h
      | pi d c => simp [Term.beq] at h
      | sort => rfl

/-- Recursive checker. 返回 some (推断的类型) 或 none。 -/
def infer : Ctx → Term → Option Term
  | _, Term.sort => some Term.sort
  | Γ, Term.var i =>
      Γ.lookup i
  | Γ, Term.pi dom cod =>
      match infer Γ dom with
      | some Term.sort =>
          match infer (dom :: Γ) cod with
          | some Term.sort => some Term.sort
          | _ => none
      | _ => none
  | Γ, Term.lam dom body =>
      match infer Γ dom with
      | some Term.sort =>
          match infer (dom :: Γ) body with
          | some bodyTy => some (Term.pi dom bodyTy)
          | none => none
      | _ => none
  | Γ, Term.app f a =>
      match infer Γ f with
      | some (Term.pi dom cod) =>
          match infer Γ a with
          | some aTy =>
              if Term.beq aTy dom then some (substitute 0 a cod) else none
          | none => none
      | _ => none

/-- `infer` 成功时给出对应的 typing derivation。 -/
theorem infer_sound
    {Γ : Ctx} {t A : Term}
    (h : infer Γ t = some A) :
    HasType Γ t A := by
  induction t generalizing Γ A with
  | var i =>
      exact HasType.varRule Γ i A h
  | app f a ihF ihA =>
      simp [infer] at h
      split at h <;> try contradiction
      rename_i dom cod hf
      split at h <;> try contradiction
      rename_i aTy ha
      split at h <;> try contradiction
      rename_i hbeq
      cases h
      exact HasType.appRule Γ f a dom cod (ihF hf) (by
        cases Term.beq_eq hbeq
        exact ihA ha)
  | lam dom body ihD ihB =>
      simp [infer] at h
      split at h <;> try contradiction
      rename_i hdom
      split at h <;> try contradiction
      rename_i bodyTy hbody
      cases h
      exact HasType.lamRule Γ dom body bodyTy (ihD hdom) (ihB hbody)
  | pi dom cod ihD ihC =>
      simp [infer] at h
      split at h <;> try contradiction
      rename_i hdom
      split at h <;> try contradiction
      rename_i hcod
      cases h
      exact HasType.piRule Γ dom cod (ihD hdom) (ihC hcod)
  | sort =>
      cases h
      exact HasType.sortRule Γ

/-- Decidable check: 给定 Γ t A, 检查 t 在 Γ 下是否类型为 A。 -/
def check (Γ : Ctx) (t A : Term) : Bool :=
  match infer Γ t with
  | some inferred => Term.beq inferred A
  | none => false

/-- Soundness: 如果 check Γ t A 返回 true，则 HasType Γ t A。 -/
theorem check_sound
    {Γ : Ctx} {t A : Term}
    (h : check Γ t A = true) :
    HasType Γ t A := by
  unfold check at h
  split at h <;> try contradiction
  rename_i inferred hinfer
  rw [← Term.beq_eq h]
  exact infer_sound hinfer

example : check [] Term.sort Term.sort = true := rfl

example : check [Term.sort] (Term.var 0) Term.sort = true := rfl

end BEDC.MetaCIC
