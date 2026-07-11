import UnifiedTheory.Dynamics.HiddenRigidity
import Mathlib.Topology.Compactness.Compact

/-!
# ch20.12 隐藏纤维 = profinite:紧 + 全不连通,故路径刚

隐藏纤维 `K∞ = ∏_p ℤ_p` 是逐坐标紧且全不连通空间的乘积。由 Tychonoff,乘积紧(定理 20.12);
乘积保持全不连通;二者合起来即 profinite。配合隐藏刚性(定理 20.3),可见连续路径进入此
profinite 纤维只能常值——solenoid 的隐藏方向刚性内核。
-/

namespace UnifiedTheory.Dynamics

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- **定理 20.12(隐藏纤维紧)**:紧隐藏坐标的乘积紧(Tychonoff)。 -/
theorem hiddenFiber_compact [∀ i, CompactSpace (X i)] : CompactSpace (∀ i, X i) :=
  inferInstance

/-- 全不连通隐藏坐标的乘积全不连通。 -/
theorem hiddenFiber_totallyDisconnected [∀ i, TotallyDisconnectedSpace (X i)] :
    TotallyDisconnectedSpace (∀ i, X i) :=
  inferInstance

/-- **profinite 隐藏纤维刚性(20.3 + 20.12 合成)**:隐藏纤维为紧 + 全不连通(profinite)时,
可见连续路径 `ℝ → K∞` 常值。 -/
theorem profinite_fiber_rigid [∀ i, CompactSpace (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
    {f : ℝ → (∀ i, X i)} (hf : Continuous f) (a b : ℝ) : f a = f b :=
  hidden_rigidity_real hf a b

end UnifiedTheory.Dynamics
