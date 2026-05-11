import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.Examples

namespace BEDC.MetaCIC

/-! ## 具体桥接例子

本文件给出一个宿主 Lean 项到 MetaCIC 项的手工编码实例, 并在
MetaCIC 的归纳 `HasType` 谓词内证明该编码项良类型。

宿主侧参照项是单宇宙层级的多态恒等函数:
`id : ∀ (T : Sort 0), T → T`。

这里不定义通用嵌入函数, 只记录一个具体编码对。证明展示该编码
不是空壳: 嵌套 lambda 项可以由当前 MetaCIC typing 规则直接检查。
-/

/-- 编码: 单 sort 范围的多态恒等函数。 -/
def encodedPolyId : Term :=
  Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))

/-- 该编码项在当前 MetaCIC 上下文表示下的 Pi 类型。 -/
def encodedPolyIdType : Term :=
  Term.pi Term.sort (Term.pi (Term.var 0) (Term.var 0))

/-- 多态恒等函数编码良类型。 -/
theorem encoded_poly_id_well_typed :
    HasType [] encodedPolyId encodedPolyIdType := by
  unfold encodedPolyId encodedPolyIdType
  apply HasType.lamRule
  · exact HasType.sortRule []
  · apply HasType.lamRule
    · apply HasType.varRule
      rfl
    · apply HasType.varRule
      rfl

end BEDC.MetaCIC
