import BEDC.FKernel.Mark

/-! Generated histories and their internal sameness relation. -/
namespace BEDC.FKernel.Hist

open BEDC.FKernel.Mark

inductive BHist where
  | Empty
  | e0 (h : BHist)
  | e1 (h : BHist)
  deriving DecidableEq, Repr

def hsame : BHist → BHist → Prop := Eq

theorem hsame_iff_eq {h k : BHist} : hsame h k ↔ h = k := by
  rfl

theorem hsame_refl : ∀ h : BHist, hsame h h := by
  intro h
  rfl

theorem hsame_symm : ∀ {h k : BHist}, hsame h k → hsame k h := by
  intro h k hs
  exact hs.symm

theorem hsame_trans : ∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c := by
  intro a b c hab hbc
  exact hab.trans hbc

theorem hsame_empty_inversion {x : BHist} : hsame .Empty x → x = .Empty := by
  intro hx
  cases hx
  rfl

theorem hsame_empty_iff {h : BHist} : hsame h BHist.Empty ↔ h = BHist.Empty := by
  constructor
  · intro hs
    cases hs
    rfl
  · intro heq
    cases heq
    rfl

theorem hsame_equivalence :
    (∀ h : BHist, hsame h h) ∧
      (∀ {h k : BHist}, hsame h k → hsame k h) ∧
      (∀ {a b c : BHist}, hsame a b → hsame b c → hsame a c) := by
  constructor
  · exact hsame_refl
  · constructor
    · exact hsame_symm
    · exact hsame_trans

theorem hsame_constructor_inversion :
    (∀ {h x : BHist}, hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k) ∧
      (∀ {h x : BHist}, hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k) := by
  constructor
  · intro h x hx
    cases hx
    exact Exists.intro h (And.intro rfl rfl)
  · intro h x hx
    cases hx
    exact Exists.intro h (And.intro rfl rfl)

theorem hsame_constructor_inversion_full :
    (∀ {h x : BHist}, hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k) ∧
      (∀ {h x : BHist}, hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k) ∧
      (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False) := by
  constructor
  · exact hsame_constructor_inversion.left
  · constructor
    · exact hsame_constructor_inversion.right
    · intro h k hs
      cases hs

theorem hsame_e1_congr {h k : BHist} : hsame h k -> hsame (.e1 h) (.e1 k) := by
  intro hs
  cases hs
  rfl

theorem hsame_e1_congruence {h k : BHist} : hsame h k -> hsame (.e1 h) (.e1 k) := by
  intro hs
  cases hs
  rfl

theorem eone_congruence {h k : BHist} : hsame h k -> hsame (.e1 h) (.e1 k) := by
  exact hsame_e1_congruence

theorem hsame_e0_congr {h k : BHist} : hsame h k -> hsame (BHist.e0 h) (BHist.e0 k) := by
  intro hs
  cases hs
  rfl

theorem hsame_e0_iff {h k : BHist} : hsame (BHist.e0 h) (BHist.e0 k) ↔ hsame h k := by
  constructor
  · intro hs
    cases hs
    rfl
  · intro hs
    cases hs
    rfl

theorem hsame_e1_iff {h k : BHist} : hsame (BHist.e1 h) (BHist.e1 k) <-> hsame h k := by
  constructor
  · intro hs
    cases hs
    rfl
  · intro hs
    cases hs
    rfl

theorem hsame_e0_inversion {h x : BHist} : hsame (.e0 h) x → ∃ k : BHist, x = .e0 k ∧ hsame h k := by
  intro hs
  cases hs
  exact Exists.intro h (And.intro rfl rfl)

theorem hsame_e0_inversion_iff {h x : BHist} :
    hsame (.e0 h) x ↔ ∃ k : BHist, x = .e0 k ∧ hsame h k := by
  constructor
  · exact hsame_e0_inversion
  · intro witness
    cases witness with
    | intro k data =>
        cases data with
        | intro hx same =>
            cases hx
            exact hsame_e0_congr same

theorem hsame_e1_inversion {h x : BHist} : hsame (.e1 h) x → ∃ k : BHist, x = .e1 k ∧ hsame h k := by
  intro hs
  cases hs
  exact Exists.intro h (And.intro rfl rfl)

theorem hsame_e1_inversion_iff {h x : BHist} :
    hsame (BHist.e1 h) x ↔ ∃ k : BHist, x = BHist.e1 k ∧ hsame h k := by
  constructor
  · exact hsame_e1_inversion
  · intro witness
    cases witness with
    | intro k data =>
        cases data with
        | intro hx same =>
            cases hx
            exact hsame_e1_congr same

theorem not_hsame_emp_e0 : ∀ {h : BHist}, hsame .Empty (.e0 h) → False := by
  intro h hs
  cases hs

theorem not_hsame_e0_empty : ∀ {h : BHist}, hsame (.e0 h) .Empty → False := by
  intro h hs
  cases hs

theorem not_hsame_emp_e1 : ∀ {h : BHist}, hsame .Empty (.e1 h) → False := by
  intro h hs
  cases hs

theorem not_hsame_e1_empty : ∀ {h : BHist}, hsame (.e1 h) .Empty → False := by
  intro h hs
  cases hs

theorem not_hsame_e0_e1 : ∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False := by
  intro h k hs
  cases hs

theorem hsame_e0_e1_iff_false {h k : BHist} :
    hsame (BHist.e0 h) (BHist.e1 k) ↔ False := by
  constructor
  · intro hs
    exact not_hsame_e0_e1 hs
  · intro hf
    exact False.elim hf

theorem not_hsame_e1_e0 : forall {h k : BHist}, hsame (.e1 h) (.e0 k) -> False := by
  intro h k hs
  cases hs

theorem hsame_no_confusion :
    (∀ {h : BHist}, hsame .Empty (.e0 h) → False) ∧
      (∀ {h : BHist}, hsame .Empty (.e1 h) → False) ∧
      (∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False) ∧
      (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False) := by
  constructor
  · exact not_hsame_emp_e0
  · constructor
    · exact not_hsame_emp_e1
    · constructor
      · exact not_hsame_e0_e1
      · exact not_hsame_e1_e0

theorem hsame_no_confusion_all :
    (∀ {h : BHist}, hsame .Empty (.e0 h) → False) ∧
      (∀ {h : BHist}, hsame .Empty (.e1 h) → False) ∧
      (∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False) ∧
      (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False) := by
  exact hsame_no_confusion

theorem history_no_confusion :
    (∀ {h : BHist}, hsame .Empty (.e0 h) → False) ∧
      (∀ {h : BHist}, hsame .Empty (.e1 h) → False) ∧
      (∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False) ∧
      (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False) := by
  exact hsame_no_confusion

theorem hsame_constructor_kind_preserved {h k : BHist} :
    hsame h k ->
      (h = BHist.Empty ∧ k = BHist.Empty) ∨
        (exists h0 : BHist, exists k0 : BHist, h = BHist.e0 h0 ∧ k = BHist.e0 k0 ∧ hsame h0 k0) ∨
        (exists h0 : BHist, exists k0 : BHist, h = BHist.e1 h0 ∧ k = BHist.e1 k0 ∧ hsame h0 k0) := by
  intro same
  cases same
  cases h
  · left
    constructor
    · rfl
    · rfl
  · right
    left
    exact Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl rfl)))
  · right
    right
    exact Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro rfl rfl)))

theorem hsame_constructor_characterization {h k : BHist} :
    hsame h k ↔ (h = BHist.Empty ∧ k = BHist.Empty) ∨
      (∃ h0 k0 : BHist, h = BHist.e0 h0 ∧ k = BHist.e0 k0 ∧ hsame h0 k0) ∨
      (∃ h0 k0 : BHist, h = BHist.e1 h0 ∧ k = BHist.e1 k0 ∧ hsame h0 k0) := by
  constructor
  · exact hsame_constructor_kind_preserved
  · intro data
    cases data with
    | inl emptyCase =>
        cases emptyCase with
        | intro left right =>
            cases left
            cases right
            rfl
    | inr stepCases =>
        cases stepCases with
        | inl zeroCase =>
            cases zeroCase with
            | intro h0 rest =>
                cases rest with
                | intro k0 fields =>
                    cases fields with
                    | intro left tail =>
                        cases tail with
                        | intro right sameTail =>
                            cases left
                            cases right
                            exact hsame_e0_congr sameTail
        | inr oneCase =>
            cases oneCase with
            | intro h0 rest =>
                cases rest with
                | intro k0 fields =>
                    cases fields with
                    | intro left tail =>
                        cases tail with
                        | intro right sameTail =>
                            cases left
                            cases right
                            exact hsame_e1_congr sameTail

theorem hsame_no_confusion_symmetric :
    (forall {h : BHist}, hsame (.e0 h) .Empty -> False) ∧
      (forall {h : BHist}, hsame (.e1 h) .Empty -> False) ∧
      (forall {h k : BHist}, hsame (.e1 h) (.e0 k) -> False) ∧
      (forall {h k : BHist}, hsame (.e0 h) (.e1 k) -> False) := by
  constructor
  · intro h hs
    cases hs
  · constructor
    · intro h hs
      cases hs
    · constructor
      · exact not_hsame_e1_e0
      · exact not_hsame_e0_e1

theorem hsame_no_confusion_complete :
    (∀ {h : BHist}, hsame .Empty (.e0 h) → False) ∧
      (∀ {h : BHist}, hsame (.e0 h) .Empty → False) ∧
      (∀ {h : BHist}, hsame .Empty (.e1 h) → False) ∧
      (∀ {h : BHist}, hsame (.e1 h) .Empty → False) ∧
      (∀ {h k : BHist}, hsame (.e0 h) (.e1 k) → False) ∧
      (∀ {h k : BHist}, hsame (.e1 h) (.e0 k) → False) := by
  constructor
  · exact not_hsame_emp_e0
  · constructor
    · exact not_hsame_e0_empty
    · constructor
      · exact not_hsame_emp_e1
      · constructor
        · intro h hs
          cases hs
        · constructor
          · exact not_hsame_e0_e1
          · exact not_hsame_e1_e0

end BEDC.FKernel.Hist
