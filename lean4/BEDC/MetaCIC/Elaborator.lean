import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Checker

namespace BEDC.MetaCIC

/-- Elaboration 失败模式. -/
inductive ElabFailure where
  | illTyped (ctx : Ctx) (t : Term)
  | unboundVariable (ctx : Ctx) (idx : Idx)
  | typeMismatch (expected actual : Term)

/-- Elaboration 结果. 成功给出推断类型和一个有界 β normal-form representative. -/
inductive ElabResult where
  | success (ty : Term) (normalForm : Term)
  | failure (mode : ElabFailure)

/-- app 分支的非递归 normalizer 核心. -/
def normalizeApp (f a nf na : Term) : Term :=
  @Term.casesOn (motive := fun _ => Term) f
    (fun _ => Term.app nf na)
    (fun _ _ => Term.app nf na)
    (fun _ body => substitute 0 a body)
    (fun _ _ => Term.app nf na)
    (Term.app nf na)

/-- 朴素 normalizer: 应用一步 β-reduction; 如果无 reduction 返回原项. -/
def normalizeOneStep : Term → Term
  | Term.var i => Term.var i
  | Term.app f a => normalizeApp f a (normalizeOneStep f) (normalizeOneStep a)
  | Term.lam d b => Term.lam (normalizeOneStep d) (normalizeOneStep b)
  | Term.pi d c => Term.pi (normalizeOneStep d) (normalizeOneStep c)
  | Term.sort => Term.sort

/-- 有界 normalizer: 最多应用 n 轮一步 β-reduction, 到达 fixpoint 时提前停止. -/
def normalizeBounded (n : Nat) (t : Term) : Term :=
  match n with
  | 0 => t
  | n + 1 =>
      let stepped := normalizeOneStep t
      if Term.beq stepped t then t else normalizeBounded n stepped

example : normalizeBounded 10 ((Term.lam Term.sort (Term.var 0)).app Term.sort) = Term.sort := rfl

/-- 主 elaborator. 用 Checker.infer 推断类型, 用 normalizeBounded 给出代表项. -/
def elaborate (Γ : Ctx) (t : Term) : ElabResult :=
  match infer Γ t with
  | some ty => ElabResult.success ty (normalizeBounded 100 t)
  | none => ElabResult.failure (ElabFailure.illTyped Γ t)

example : elaborate [] Term.sort = ElabResult.success Term.sort Term.sort := rfl

example : elaborate [Term.sort] (Term.var 0) = ElabResult.success Term.sort (Term.var 0) := rfl

end BEDC.MetaCIC
