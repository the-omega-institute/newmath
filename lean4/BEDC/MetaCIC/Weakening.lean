import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

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

/--
要求的最外层弱化形状在当前规则下不是定理。

lambda 的 body 中 `var 0` 被 binder 保护而不会被 `shift 0 1` 改写,
但 cons 后 lookup 顶部 binder 类型会穿过新增上下文层, 返回提升后的类型。
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

end BEDC.MetaCIC
