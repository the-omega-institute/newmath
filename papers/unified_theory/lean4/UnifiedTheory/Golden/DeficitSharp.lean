import UnifiedTheory.Golden.BeattyDeficit

/-!
# 亏空三值定界的 sharp 性(生成式发现)

源文档只证亏空 `cDef ∈ {−1,0,1}`(上界)。本文件补上自然的**取尽性**:三个值都被实际取到,
故 Beatty 亏空的值域**恰为** `{−1,0,1}`——三值定界是 sharp 的。显式见证由具体的 `⌊nφ⌋`
计算给出。这是"直觉(界是否 sharp?)→ 形式化(是,给见证)"生成循环的一个产物,不在源文档中。
-/

namespace UnifiedTheory

open Real

private theorem gr_lo : (8 : ℝ) / 5 ≤ Real.goldenRatio := by
  nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]

private theorem gr_hi : Real.goldenRatio < 13 / 8 := by
  nlinarith [Real.goldenRatio_sq, Real.goldenRatio_pos]

/-- 位移读数在具体点的值:给定 `⌊(v+1)φ⌋ = m` 的窗口界即得 `S v = m − 1`。 -/
private theorem Sval (v : ℕ) (m : ℤ)
    (hlo : (m : ℝ) ≤ ((v : ℝ) + 1) * Real.goldenRatio)
    (hhi : ((v : ℝ) + 1) * Real.goldenRatio < m + 1) : S v = m - 1 := by
  unfold S
  rw [Int.floor_eq_iff.mpr ⟨hlo, hhi⟩]

theorem S_at0 : S 0 = 0 := by
  have := Sval 0 1 (by push_cast; nlinarith [gr_lo]) (by push_cast; nlinarith [gr_hi])
  simpa using this

theorem S_at1 : S 1 = 2 := by
  have := Sval 1 3 (by push_cast; nlinarith [gr_lo]) (by push_cast; nlinarith [gr_hi])
  simpa using this

theorem S_at2 : S 2 = 3 := by
  have := Sval 2 4 (by push_cast; nlinarith [gr_lo]) (by push_cast; nlinarith [gr_hi])
  simpa using this

theorem S_at4 : S 4 = 7 := by
  have := Sval 4 8 (by push_cast; nlinarith [gr_lo]) (by push_cast; nlinarith [gr_hi])
  simpa using this

theorem cDef_00 : cDef 0 0 = 0 := by simp [cDef, S_at0]

theorem cDef_11 : cDef 1 1 = 1 := by
  have h : (1 : ℕ) + 1 = 2 := rfl
  simp only [cDef, h, S_at1, S_at2]; norm_num

theorem cDef_22 : cDef 2 2 = -1 := by
  have h : (2 : ℕ) + 2 = 4 := rfl
  simp only [cDef, h, S_at2, S_at4]; norm_num

/-- **生成式定理(三值 sharp)**:亏空取到全部三个值 `−1, 0, 1`。与 `cDef_mem`(∈{−1,0,1})
合观,Beatty 亏空的值域**恰为** `{−1,0,1}`——三值定界不可再收紧。 -/
theorem deficit_trichotomy_sharp :
    (∃ a b, cDef a b = -1) ∧ (∃ a b, cDef a b = 0) ∧ (∃ a b, cDef a b = 1) :=
  ⟨⟨2, 2, cDef_22⟩, ⟨0, 0, cDef_00⟩, ⟨1, 1, cDef_11⟩⟩

end UnifiedTheory
