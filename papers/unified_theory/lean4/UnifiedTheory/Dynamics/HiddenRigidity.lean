import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# ch20.3 隐藏刚性

可见—隐藏动力学的刚性核心:一条连续路径若取值于**全不连通**的隐藏空间(如 solenoid 的
纤维 `K∞ = ∏_p ℤ_p`,profinite 群),则**常值**——可见轨迹在隐藏纤维上只能离散跳转,不能
连续漂移。抽象形式:从任一 preconnected 空间到全不连通空间的连续映射常值。
-/

namespace UnifiedTheory.Dynamics

/-- **隐藏刚性(抽象核心)**:preconnected 定义域 + 全不连通值域 ⟹ 连续映射常值。 -/
theorem hidden_rigidity {Y X : Type*} [TopologicalSpace Y] [PreconnectedSpace Y]
    [TopologicalSpace X] [TotallyDisconnectedSpace X]
    {f : Y → X} (hf : Continuous f) (a b : Y) : f a = f b := by
  have hpre : IsPreconnected (Set.range f) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image f hf.continuousOn
  exact hpre.subsingleton (Set.mem_range_self a) (Set.mem_range_self b)

/-- **定理 20.3(隐藏刚性)**:连通实区间(以 `ℝ` 为模型)到全不连通隐藏空间 `K∞` 的
连续路径常值。这是"隐藏变化只能离散跳转或搭载整体相位路径"(推论 20.4)的刚性内核。 -/
theorem hidden_rigidity_real {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    {f : ℝ → X} (hf : Continuous f) (a b : ℝ) : f a = f b :=
  hidden_rigidity hf a b

end UnifiedTheory.Dynamics
