import UnifiedTheory.Foundation.History

/-!
# ch18 成本时间之矢(定理 18.7/18.11)

时间之矢居账本层:每次生成严格增加成本(此处成本 = 事件历史长度),故生成不可逆——
生成后的历史永不等于生成前(推论 18.12:不可逆性移居账本层)。这把生成层与"时间 = 账本
增长"的立场(第三十章)连起来。
-/

namespace UnifiedTheory.EventHist

variable {Op Arg : Type u}

/-- **定理 18.7/18.11(成本时间之矢)**:生成严格增加成本。 -/
theorem cost_lt_generate (h : EventHist Op Arg) (u : Event Op Arg) :
    h.length < (generate h u).length := by
  rw [generate_length]; omega

/-- **推论 18.12(不可逆)**:生成后的历史永不等于原历史(时间之矢)。 -/
theorem generate_ne (h : EventHist Op Arg) (u : Event Op Arg) :
    generate h u ≠ h := by
  intro heq
  have hlt := cost_lt_generate h u
  rw [heq] at hlt
  omega

end UnifiedTheory.EventHist
