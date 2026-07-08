import Mathlib.Computability.PartrecCode
import UnifiedTheory.SelfCode.Diagonal

/-!
# ch16 Kleene 不动点(定理 16.1')

SC-1 把第十六章的机器层从"运行总终止"改为部分递归语义。`Nat.Partrec.Code.eval`
解释为部分函数 `ℕ →. ℕ`, 所以 Kleene 不动点只断言行为相等, 不断言任一运行总终止。
-/

namespace UnifiedTheory.SelfCode

/--
**定理 16.1'(Kleene 不动点, 无条件)**: 对内核自代码层, 任一可计算码变换存在行为不动点。

这里的语法变换 `f` 是总函数, 可计算性由 `Computable f` 给出; 结论给出码 `c`, 使
`f c` 与 `c` 作为部分函数的语义完全相等。证明直接使用 mathlib 的 Kleene 递归定理,
其核心是 s-m-n 与通用机, 不需要"总终止"公设 U。
-/
theorem kleene_fixed_point {f : Nat.Partrec.Code → Nat.Partrec.Code} (hf : Computable f) :
    ∃ c : Nat.Partrec.Code, (f c).eval = c.eval :=
  Nat.Partrec.Code.fixed_point hf

/--
带输入参数的 Kleene 不动点形式: 若二元部分函数族 `f` 是部分递归的, 则存在码 `c`,
其部分函数语义正好等于 `f c`。
-/
theorem kleene_fixed_point₂ {f : Nat.Partrec.Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Nat.Partrec.Code, c.eval = f c :=
  Nat.Partrec.Code.fixed_point₂ hf

/-!
SC-1 的第十六章结论由两条无条件事实组成: 本文件的 Kleene 不动点给出部分递归语义中的
行为不动点, `SelfCode.Diagonal` 的 Cantor 对角给出自编码性质层不可由分类器穷尽, 也不可
由解码器单射覆盖。由此, 机器公设 U 不再属于内核公设表; 其残余只保留为 17.8 的算术化余项,
即 Gödel 第二不完全性方向的外部形式化问题。
-/

/--
文档定理: SC-1 的核心第十六章事实同时成立, 且均不需要总终止公设 U。
-/
theorem sc1_chapter16_unconditional
    {f : Nat.Partrec.Code → Nat.Partrec.Code} (hf : Computable f)
    {X : Type*} (classify : X → Set X) (decode : Set X → X) :
    (∃ c : Nat.Partrec.Code, (f c).eval = c.eval) ∧
      ¬ Function.Surjective classify ∧
      ¬ Function.Injective decode :=
  ⟨kleene_fixed_point hf, no_classifier_surjective classify, no_decoder_injective decode⟩

end UnifiedTheory.SelfCode
