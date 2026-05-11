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

-- Term.beq_eq soundness lemma 暂未给出: simp-based proof 拉入了 propext;
-- 重写为 pure CIC 推理是 V4 工作。Checker.lean 的当前形态只提供 def，不主张 soundness。

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

-- infer_sound theorem 暂未给出: 同上 (simp-based 拉入 propext, V4 工作)。

/-- Decidable check: 给定 Γ t A, 检查 t 在 Γ 下是否类型为 A。 -/
def check (Γ : Ctx) (t A : Term) : Bool :=
  match infer Γ t with
  | some inferred => Term.beq inferred A
  | none => false

-- check_sound 同上: 依赖 infer_sound + Term.beq_eq, 都是 V4 工作。

example : check [] Term.sort Term.sort = true := rfl

example : check [Term.sort] (Term.var 0) Term.sort = true := rfl

end BEDC.MetaCIC
