import UnifiedTheory.Golden.BeattyDeficit

/-!
# n 元 Beatty-floor 亏空

本文件把二元 Beatty 亏空 `cDef` 扩展为列表亏空 `Cn`。核心分解是
`Cn (v :: vs) = cDef v vs.sum + Cn vs`,因此 n 元亏空由相邻并入步骤的二元
亏空累积而成。
-/

namespace UnifiedTheory

/-- n 元 Beatty-floor 亏空。 -/
noncomputable def Cn (vs : List ℕ) : ℤ :=
  (vs.map S).sum - S vs.sum

private theorem S_zero : S 0 = 0 := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : ℤ) := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor
    · exact le_of_lt Real.one_lt_goldenRatio
    · exact Real.goldenRatio_lt_two
  simp [S, hfloor]

/-- 空列表亏空为零。 -/
@[simp] theorem Cn_nil : Cn [] = 0 := by
  simp [Cn, S_zero]

/-- 单项列表亏空为零。 -/
@[simp] theorem Cn_singleton (v : ℕ) : Cn [v] = 0 := by
  simp [Cn]

/-- 二元列表亏空与 Beatty 二元进位亏空相同。 -/
theorem Cn_pair (a b : ℕ) : Cn [a, b] = cDef a b := by
  simp [Cn, cDef]

/-- 把一个新项并入列表时,n 元亏空按二元亏空分解。 -/
theorem Cn_cons (v : ℕ) (vs : List ℕ) :
    Cn (v :: vs) = cDef v vs.sum + Cn vs := by
  unfold Cn cDef
  simp [List.sum_cons]
  ring

private theorem cDef_abs_le_one (a b : ℕ) : |cDef a b| ≤ (1 : ℤ) := by
  obtain h | h | h := cDef_mem a b
  · simp [h]
  · simp [h]
  · simp [h]

/-- n 元亏空的逐步对称界:每次并入至多贡献一个单位亏空。 -/
theorem Cn_abs_le (vs : List ℕ) :
    |Cn vs| ≤ ((vs.length - 1 : ℕ) : ℤ) := by
  induction vs with
  | nil =>
      simp
  | cons v tail ih =>
      cases tail with
      | nil =>
          simp
      | cons w ws =>
          have hstep : Cn (v :: w :: ws) = cDef v (w :: ws).sum + Cn (w :: ws) :=
            Cn_cons v (w :: ws)
          have htail : |Cn (w :: ws)| ≤ (ws.length : ℤ) := by
            simpa using ih
          have htri :
              |Cn (v :: w :: ws)| ≤
                |cDef v (w :: ws).sum| + |Cn (w :: ws)| := by
            rw [hstep]
            exact abs_add_le _ _
          have hbound : |Cn (v :: w :: ws)| ≤ (1 : ℤ) + ws.length := by
            calc
              |Cn (v :: w :: ws)|
                  ≤ |cDef v (w :: ws).sum| + |Cn (w :: ws)| := htri
              _ ≤ (1 : ℤ) + ws.length :=
                  add_le_add (cDef_abs_le_one v (w :: ws).sum) htail
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using hbound

end UnifiedTheory
