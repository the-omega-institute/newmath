import Mathlib.Data.Nat.Find
import Mathlib.Logic.Basic

/-!
# 可证伪性

本文件形式化账本纪律 D 的可证伪性化身: 有限读数全称断言的否证有
第 0 层有限证书, 即一个最小反例。它对应主定理自审中“每个非零
residual 要么被有限读数检出要么入账”的检出半。
-/

namespace UnifiedTheory.Kernel

/-- 若关于有限读数的全称断言为假, 则存在一个具体反例。 -/
theorem exists_counterexample {p : ℕ → Prop} (h : ¬ ∀ n, p n) : ∃ n, ¬ p n :=
  not_forall.mp h

/--
定理 13.2 的核心形式: 对可判定的有限读数谓词, 若全称断言为假,
则存在最小反例; 这个最小反例及其之前读数全真的事实组成第 0 层
有限证书。
-/
theorem least_counterexample {p : ℕ → Prop} [DecidablePred p] (h : ¬ ∀ n, p n) :
    ∃ n, ¬ p n ∧ ∀ m, m < n → p m := by
  let H : ∃ n, (fun n => ¬ p n) n := exists_counterexample h
  let N := Nat.find H
  refine ⟨N, Nat.find_spec H, ?_⟩
  intro m hm
  exact not_not.mp (Nat.find_min H hm)

end UnifiedTheory.Kernel
