import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- de Bruijn index 的结构布尔相等。 -/
def idxBeq (i j : Idx) : Bool :=
  Nat.rec
    (motive := fun _ => Idx → Bool)
    (fun j =>
      @Nat.casesOn (motive := fun _ => Bool) j true (fun _ => false))
    (fun _ ih j =>
      @Nat.casesOn (motive := fun _ => Bool) j false (fun j' => ih j'))
    i j

/-- var 分支的二项比较, 用 casesOn 固定纯消去路径。 -/
def Term.beqVar (i : Idx) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun j => idxBeq i j)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    false

/-- app 分支的二项比较。 -/
def Term.beqApp (bf ba : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun f' a' => bf f' && ba a')
    (fun _ _ => false)
    (fun _ _ => false)
    false

/-- lam 分支的二项比较。 -/
def Term.beqLam (bd bb : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun d' b' => bd d' && bb b')
    (fun _ _ => false)
    false

/-- pi 分支的二项比较。 -/
def Term.beqPi (bd bc : Term → Bool) (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun d' c' => bd d' && bc c')
    false

/-- sort 分支的二项比较。 -/
def Term.beqSort (y : Term) : Bool :=
  @Term.casesOn (motive := fun _ => Bool) y
    (fun _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ => false)
    true

/-- 比较两个 Term 是否结构相等。 -/
def Term.beq : Term → Term → Bool
  | Term.var i => Term.beqVar i
  | Term.app f a => Term.beqApp (Term.beq f) (Term.beq a)
  | Term.lam d b => Term.beqLam (Term.beq d) (Term.beq b)
  | Term.pi d c => Term.beqPi (Term.beq d) (Term.beq c)
  | Term.sort => Term.beqSort

theorem idxBeq_eq {i j : Idx} (h : idxBeq i j = true) : i = j := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => rfl
      | succ _ => cases h
  | succ i ih =>
      cases j with
      | zero => cases h
      | succ j =>
          cases ih h
          rfl

theorem bool_and_left_true : {a b : Bool} → (a && b) = true → a = true
  | false, _, h => nomatch h
  | true, _, _ => rfl

theorem bool_and_right_true : {a b : Bool} → (a && b) = true → b = true
  | false, _, h => nomatch h
  | true, _, h => h

theorem Term.beq_eq {x y : Term} (h : Term.beq x y = true) : x = y := by
  induction x generalizing y with
  | var i =>
      cases y with
      | var j =>
          cases idxBeq_eq h
          rfl
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
      | sort => cases h
  | app f a ihf iha =>
      cases y with
      | var _ => cases h
      | app f' a' =>
          cases ihf (bool_and_left_true h)
          cases iha (bool_and_right_true h)
          rfl
      | lam _ _ => cases h
      | pi _ _ => cases h
      | sort => cases h
  | lam d b ihd ihb =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam d' b' =>
          cases ihd (bool_and_left_true h)
          cases ihb (bool_and_right_true h)
          rfl
      | pi _ _ => cases h
      | sort => cases h
  | pi d c ihd ihc =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi d' c' =>
          cases ihd (bool_and_left_true h)
          cases ihc (bool_and_right_true h)
          rfl
      | sort => cases h
  | sort =>
      cases y with
      | var _ => cases h
      | app _ _ => cases h
      | lam _ _ => cases h
      | pi _ _ => cases h
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

-- infer_sound 需要逐分支构造 HasType, 当前文件只主张 checker 定义与 beq soundness。

/-- Decidable check: 给定 Γ t A, 检查 t 在 Γ 下是否类型为 A。 -/
def check (Γ : Ctx) (t A : Term) : Bool :=
  match infer Γ t with
  | some inferred => Term.beq inferred A
  | none => false

-- check_sound 依赖 infer_sound 的逐分支证明, 当前文件不主张 check soundness。

example : check [] Term.sort Term.sort = true := rfl

example : check [Term.sort] (Term.var 0) Term.sort = true := rfl

end BEDC.MetaCIC
