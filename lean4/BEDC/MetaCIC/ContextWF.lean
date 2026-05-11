import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

/-- 上下文良构: 空上下文良构; 在已良构的 Γ 上 cons 一个在 Γ 下类型为 sort 的项, 良构。
    这阻止形如 [var 1] 这种引用不存在变量的 ill-typed context。 -/
inductive WellFormedCtx : Ctx → Prop
  | wfNil : WellFormedCtx []
  | wfCons {Γ : Ctx} {T : Term} :
      WellFormedCtx Γ →
      HasType Γ T Term.sort →
      WellFormedCtx (T :: Γ)

end BEDC.MetaCIC
