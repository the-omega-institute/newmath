import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# ch3 单位性判据:抽象重写与 Newman 引理(定理 3.2)

文档定理 3.2:终止且局部合流的重写系统中每条历史恰有一个标准形。这里把它做成泛型的抽象
重写理论(不特化到历史):`Terminates`(归约关系良基)+ `LocallyConfluent`(单步分叉可 join)
⇒ `Confluent`(多步分叉可 join,Newman 引理)⇒ 标准形存在且唯一。mathlib 无 generic Newman,
故在 `Relation.ReflTransGen` + `WellFounded` 上自建。
-/

namespace UnifiedTheory.Rewriting

variable {α : Type u} (r : α → α → Prop)

/-- 多步归约:自反传递闭包。 -/
abbrev Star := Relation.ReflTransGen r

/-- 标准形:无后继。 -/
def Normal (a : α) : Prop := ∀ b, ¬ r a b

/-- 可 join:存在公共归约目标。 -/
def Joinable (a b : α) : Prop := ∃ c, Star r a c ∧ Star r b c

/-- 局部合流:单步分叉可 join。 -/
def LocallyConfluent : Prop := ∀ a b c, r a b → r a c → Joinable r b c

/-- 合流:多步分叉可 join。 -/
def Confluent : Prop := ∀ a b c, Star r a b → Star r a c → Joinable r b c

/-- 终止:归约关系良基(无无穷归约链)。 -/
def Terminates : Prop := WellFounded (fun b a => r a b)

variable {r}

/-- **Newman 引理**(定理 3.2 核心):终止 + 局部合流 ⇒ 合流。 -/
theorem newman_confluent (hwf : Terminates r) (hlc : LocallyConfluent r) :
    Confluent r := fun a =>
  hwf.induction (C := fun a => ∀ b c, Star r a b → Star r a c → Joinable r b c) a
    (fun a IH b c hab hac => by
    rcases hab.cases_head with rfl | ⟨a₁, ha1, h1b⟩
    · exact ⟨c, hac, .refl⟩
    rcases hac.cases_head with rfl | ⟨a₂, ha2, h2c⟩
    · exact ⟨b, .refl, hab⟩
    obtain ⟨d, h1d, h2d⟩ := hlc a a₁ a₂ ha1 ha2
    obtain ⟨e, hbe, hde⟩ := IH a₁ ha1 b d h1b h1d
    obtain ⟨g, hcg, heg⟩ := IH a₂ ha2 c e h2c (h2d.trans hde)
    exact ⟨g, hbe.trans heg, hcg⟩)

/-- 合流下标准形唯一。 -/
theorem normal_form_unique_of_confluent (hc : Confluent r)
    {a n₁ n₂ : α} (h1 : Star r a n₁) (hn1 : Normal r n₁)
    (h2 : Star r a n₂) (hn2 : Normal r n₂) : n₁ = n₂ := by
  obtain ⟨d, hd1, hd2⟩ := hc a n₁ n₂ h1 h2
  have e1 : n₁ = d := by
    rcases hd1.cases_head with rfl | ⟨x, hx, _⟩
    · rfl
    · exact absurd hx (hn1 x)
  have e2 : n₂ = d := by
    rcases hd2.cases_head with rfl | ⟨x, hx, _⟩
    · rfl
    · exact absurd hx (hn2 x)
  rw [e1, e2]

/-- 终止 + 局部合流 ⇒ 每个元素有唯一标准形(定理 3.2)。 -/
theorem exists_unique_normal_form (hwf : Terminates r) (hlc : LocallyConfluent r)
    (a : α) : ∃! n, Star r a n ∧ Normal r n := by
  have hex : ∀ a, ∃ n, Star r a n ∧ Normal r n := fun a =>
    hwf.induction (C := fun a => ∃ n, Star r a n ∧ Normal r n) a (fun a IH => by
      by_cases h : ∃ b, r a b
      · obtain ⟨b, hb⟩ := h
        obtain ⟨n, hn, hnn⟩ := IH b hb
        exact ⟨n, (Relation.ReflTransGen.single hb).trans hn, hnn⟩
      · exact ⟨a, .refl, fun b hb => h ⟨b, hb⟩⟩)
  obtain ⟨n, hn, hnn⟩ := hex a
  refine ⟨n, ⟨hn, hnn⟩, ?_⟩
  rintro m ⟨hm, hmn⟩
  exact normal_form_unique_of_confluent (newman_confluent hwf hlc) hm hmn hn hnn

end UnifiedTheory.Rewriting
