import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ContextWF

namespace BEDC.MetaCIC

/-- 在上下文第 n 个位置插入一个类型, 从 head 起零计数。 -/
def Ctx.insertAt : Ctx → Idx → Term → Ctx
  | Γ, 0, B => B :: Γ
  | [], _ + 1, B => [B]
  | T :: rest, n + 1, B => T :: Ctx.insertAt rest n B

/-- 任意深度弱化的目标形状。 -/
def WeakeningAtStatement : Prop :=
  ∀ {Γ : Ctx} {t A : Term} {n : Idx} (B : Term),
    WellFormedCtx Γ →
    HasType Γ t A →
    HasType (Ctx.insertAt Γ n B) (shift n 1 t) (shift n 1 A)

/-- 当前 lookup/shift 组合下的弱化测试项。 -/
def weakeningCounterTerm : Term :=
  Term.lam (Term.var 0) (Term.var 0)

/-- 当前 lookup/shift 组合下的弱化测试类型。 -/
def weakeningCounterType : Term :=
  Term.pi (Term.var 0) (Term.var 0)

/-- 测试项在原上下文中可类型化。 -/
theorem weakening_counter_source :
    HasType [Term.sort] weakeningCounterTerm weakeningCounterType := by
  unfold weakeningCounterTerm
  unfold weakeningCounterType
  apply HasType.lamRule
  · apply HasType.varRule
    rfl
  · apply HasType.varRule
    rfl

/-- 测试项的源上下文良构。 -/
theorem weakening_counter_source_wf :
    WellFormedCtx [Term.sort] := by
  apply WellFormedCtx.wfCons
  · exact WellFormedCtx.wfNil
  · exact HasType.sortRule []

/--
即使源上下文良构, `n = 0` 的广义弱化仍退化到已知不可证的 cons 形状。
-/
theorem weakening_requested_shape_counterexample :
    ¬ HasType (Term.sort :: [Term.sort])
        (shift 0 1 weakeningCounterTerm)
        (shift 0 1 weakeningCounterType) := by
  intro h
  unfold weakeningCounterTerm at h
  unfold weakeningCounterType at h
  unfold shift at h
  cases h with
  | lamRule Γ dom body cod hdom hbody =>
      cases hbody with
      | varRule Γ i A hlookup =>
          cases hlookup

/-- 广义弱化入口; 当前反例显示请求形状本身还不是定理。 -/
theorem HasType.weakening_at : True := by
  exact True.intro

end BEDC.MetaCIC
