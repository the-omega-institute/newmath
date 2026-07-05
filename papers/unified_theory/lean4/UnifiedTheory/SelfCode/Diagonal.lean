import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic

/-!
# ch16 对角与不动点(定理 16.2–16.3)

自代码层的对角论证:把载体元素当作性质(`Set X`)的索引,任何"分类器" `classify : X → Set X`
都不满射——**性质层不被任一分类器穷尽**(主定理 28.1 第 2 条自编码 / 评注 28.4 甲之"对角使无
分类器穷尽性质层")。显式对角性质 `{y | y ∉ classify y}` 永不被命中(Cantor 对角);对偶地,
任何"解码器" `Set X → X` 都不单射。
-/

namespace UnifiedTheory.SelfCode

/-- **定理 16.2(对角)**:任何分类器 `classify : X → Set X` 不满射。 -/
theorem no_classifier_surjective {X : Type*} (classify : X → Set X) :
    ¬ Function.Surjective classify :=
  Function.cantor_surjective classify

/-- 显式对角见证:对角性质 `{y | y ∉ classify y}` 不是任一索引 `x` 的分类值。 -/
theorem diagonal_not_classified {X : Type*} (classify : X → Set X) (x : X) :
    classify x ≠ {y | y ∉ classify y} := by
  intro h
  have hx : (x ∈ classify x) ↔ (x ∉ classify x) := Set.ext_iff.mp h x
  exact iff_not_self hx

/-- **定理 16.3(不可达对偶)**:任何解码器 `decode : Set X → X` 不单射。 -/
theorem no_decoder_injective {X : Type*} (decode : Set X → X) :
    ¬ Function.Injective decode :=
  Function.cantor_injective decode

end UnifiedTheory.SelfCode
