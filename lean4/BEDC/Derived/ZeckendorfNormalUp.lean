import BEDC.Derived.AxisZeckendorf.Zeckendorf

namespace BEDC.Derived.ZeckendorfNormalUp

open BEDC.FKernel.Hist

theorem ZNormal_hsame_transport {h k : BHist} :
    BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal h -> hsame h k ->
      BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal k ∧
        (∀ t : BHist, k = BHist.e1 t ->
          (t = BHist.Empty ∨
            ∃ u : BHist, t = BHist.e0 u ∧
              BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal (BHist.e0 u))) := by
  intro normal sameHK
  cases sameHK
  constructor
  · exact normal
  · intro t ht
    cases ht
    exact
      (BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal_adjacent_one_inversion normal).left

theorem ZNormal_public_normal_form_boundary {h : BHist} :
    BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal h ->
      h = BHist.Empty ∨
        (exists t : BHist,
          h = BHist.e0 t ∧ BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal t) ∨
          h = BHist.e1 BHist.Empty ∨
            (exists t : BHist,
              h = BHist.e1 (BHist.e0 t) ∧
                BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal (BHist.e0 t)) := by
  intro normal
  cases normal with
  | empty =>
      exact Or.inl rfl
  | e0 tailNormal =>
      exact Or.inr (Or.inl (Exists.intro _ (And.intro rfl tailNormal)))
  | e1_after_empty =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | e1_after_e0 tailNormal =>
      exact Or.inr (Or.inr (Or.inr (Exists.intro _ (And.intro rfl tailNormal))))

end BEDC.Derived.ZeckendorfNormalUp
