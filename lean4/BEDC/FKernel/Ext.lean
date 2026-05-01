import BEDC.FKernel.Mark
import BEDC.FKernel.Hist

/-! Relational extension of a history by one emitted mark. -/
namespace BEDC.FKernel.Ext

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist

inductive Ext : BHist → BMark → BHist → Prop where
  | e0 (h : BHist) : Ext h .b0 (.e0 h)
  | e1 (h : BHist) : Ext h .b1 (.e1 h)

theorem ext_generation_rules (h : BHist) :
    Ext h BMark.b0 (BHist.e0 h) /\ Ext h BMark.b1 (BHist.e1 h) := by
  constructor
  · exact Ext.e0 h
  · exact Ext.e1 h

theorem ext_total : ∀ (h : BHist) (m : BMark), ∃ r : BHist, Ext h m r := by
  intro h m
  cases m
  · exact Exists.intro (BHist.e0 h) (Ext.e0 h)
  · exact Exists.intro (BHist.e1 h) (Ext.e1 h)

theorem ext_deterministic :
    ∀ {h r r' : BHist} {m : BMark}, Ext h m r → Ext h m r' → hsame r r' := by
  intro h r r' m hr hr'
  cases hr <;> cases hr' <;> rfl

theorem ext_determinacy_up_to_hsame_spine {h r r' : BHist} {m : BMark} :
    Ext h m r -> Ext h m r' -> hsame r r' := by
  intro left right
  exact ext_deterministic left right

theorem proof_sprint_extension_determinacy {h r r' : BHist} {m : BMark} :
    Ext h m r → Ext h m r' → hsame r r' := by
  intro left right
  exact ext_deterministic left right

theorem ext_mark_deterministic_from_result :
    ∀ {h r : BHist} {m n : BMark}, Ext h m r → Ext h n r → msame m n := by
  intro h r m n hr hs
  cases hr <;> cases hs <;> rfl

theorem ext_source_deterministic_from_result :
    ∀ {h h' r : BHist} {m : BMark}, Ext h m r → Ext h' m r → hsame h h' := by
  intro h h' r m left right
  cases left <;> cases right <;> rfl

theorem ext_result_injective_pair {h h' r : BHist} {m m' : BMark} :
    Ext h m r -> Ext h' m' r -> hsame h h' ∧ msame m m' := by
  intro left right
  cases left <;> cases right <;> constructor <;> rfl

theorem ext_result_hsame_injective_pair {h h' r r' : BHist} {m m' : BMark} :
    Ext h m r -> Ext h' m' r' -> hsame r r' -> hsame h h' ∧ msame m m' := by
  intro left right sameResult
  cases left
  · cases right
    · constructor
      · exact Iff.mp hsame_e0_iff sameResult
      · rfl
    · exact False.elim (not_hsame_e0_e1 sameResult)
  · cases right
    · exact False.elim (not_hsame_e1_e0 sameResult)
    · constructor
      · exact Iff.mp hsame_e1_iff sameResult
      · rfl

theorem ext_cross_mark_result_impossible {h r : BHist} :
    Ext h BMark.b0 r -> Ext h BMark.b1 r -> False := by
  intro left right
  cases left
  cases right

theorem ext_respects_sameness :
    ∀ {h h' r r' : BHist} {m m' : BMark},
      hsame h h' → msame m m' → Ext h m r → Ext h' m' r' → hsame r r' := by
  intro h h' r r' m m' hh hm hr hr'
  cases hh
  cases hm
  cases hr <;> cases hr' <;> rfl

theorem ext_respects_internal_sameness_spine {h k r s : BHist} {m n : BMark} :
    msame m n → hsame h k → Ext h m r → Ext k n s → hsame r s := by
  intro hm hh left right
  cases hm
  cases hh
  cases left <;> cases right <;> rfl

theorem ext_respects_mark_sameness :
    forall {h r r' : BHist} {m n : BMark}, msame m n -> Ext h m r -> Ext h n r' -> hsame r r' := by
  intro h r r' m n hm hr hr'
  cases hm
  cases hr <;> cases hr' <;> rfl

theorem ext_constructor_inversion {h r : BHist} {m : BMark} :
    Ext h m r ->
      (m = BMark.b0 /\ r = BHist.e0 h) \/ (m = BMark.b1 /\ r = BHist.e1 h) := by
  intro hr
  cases hr
  ·
      exact Or.inl (And.intro rfl rfl)
  ·
      exact Or.inr (And.intro rfl rfl)

theorem ext_constructor_characterization {h r : BHist} {m : BMark} :
    Ext h m r ↔ (m = BMark.b0 ∧ r = BHist.e0 h) ∨ (m = BMark.b1 ∧ r = BHist.e1 h) := by
  constructor
  ·
      intro hr
      cases hr
      ·
          exact Or.inl (And.intro rfl rfl)
      ·
          exact Or.inr (And.intro rfl rfl)
  ·
      intro hcase
      cases hcase with
      | inl left =>
          cases left with
          | intro hm hr =>
              cases hm
              cases hr
              exact Ext.e0 h
      | inr right =>
          cases right with
          | intro hm hr =>
              cases hm
              cases hr
              exact Ext.e1 h

theorem ext_result_constructor_iff {h tail : BHist} :
    (∀ {m : BMark}, Ext h m (BHist.e0 tail) ↔ m = BMark.b0 ∧ hsame h tail) ∧
      (∀ {m : BMark}, Ext h m (BHist.e1 tail) ↔ m = BMark.b1 ∧ hsame h tail) := by
  constructor
  · intro m
    constructor
    · intro hx
      cases hx
      exact ⟨rfl, rfl⟩
    · intro data
      cases data with
      | intro hm hs =>
          cases hm
          cases hs
          exact Ext.e0 h
  · intro m
    constructor
    · intro hx
      cases hx
      exact ⟨rfl, rfl⟩
    · intro data
      cases data with
      | intro hm hs =>
          cases hm
          cases hs
          exact Ext.e1 h

theorem ext_result_for_mark {h r : BHist} {m : BMark} :
    Ext h m r → (m = BMark.b0 → r = BHist.e0 h) ∧ (m = BMark.b1 → r = BHist.e1 h) := by
  intro hr
  constructor
  · intro hm
    cases hr
    · rfl
    · cases hm
  · intro hm
    cases hr
    · cases hm
    · rfl

theorem ext_b0_result_hsame {h r : BHist} :
    Ext h BMark.b0 r -> hsame r (BHist.e0 h) := by
  intro hr
  cases hr
  rfl

theorem ext_b1_result_hsame {h r : BHist} :
    Ext h BMark.b1 r -> hsame r (BHist.e1 h) := by
  intro hr
  cases hr
  rfl

theorem ext_result_ne_empty {h r : BHist} {m : BMark} :
    Ext h m r -> hsame r BHist.Empty -> False := by
  intro hr sameEmpty
  cases hr
  · exact not_hsame_e0_empty sameEmpty
  · exact not_hsame_e1_empty sameEmpty

theorem ext_same_source_cross_mark_results_not_hsame {h r0 r1 : BHist} :
    Ext h BMark.b0 r0 -> Ext h BMark.b1 r1 -> hsame r0 r1 -> False := by
  intro left right same
  cases left
  cases right
  exact not_hsame_e0_e1 same

end BEDC.FKernel.Ext
