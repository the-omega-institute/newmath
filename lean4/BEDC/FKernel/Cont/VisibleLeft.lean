import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem append_visible_left_empty_absurd {h k : BHist} :
    (hsame (append (BHist.e0 h) k) BHist.Empty -> False) ∧
      (hsame (append (BHist.e1 h) k) BHist.Empty -> False) := by
  constructor
  · intro same
    cases k with
    | Empty =>
        exact not_hsame_e0_empty same
    | e0 k =>
        exact not_hsame_e0_empty same
    | e1 k =>
        exact not_hsame_e1_empty same
  · intro same
    cases k with
    | Empty =>
        exact not_hsame_e1_empty same
    | e0 k =>
        exact not_hsame_e0_empty same
    | e1 k =>
        exact not_hsame_e1_empty same

theorem append_visible_left_same_tail_tag_separation {h0 h1 k : BHist} :
    hsame (append (BHist.e0 h0) k) (append (BHist.e1 h1) k) -> False := by
  intro same
  induction k with
  | Empty =>
      exact not_hsame_e0_e1 same
  | e0 k ih =>
      exact ih (BHist.e0.inj same)
  | e1 k ih =>
      exact ih (BHist.e1.inj same)

theorem append_visible_left_same_tag_tail_cancel :
    (forall {h0 h1 k : BHist},
      hsame (append (BHist.e0 h0) k) (append (BHist.e0 h1) k) -> hsame h0 h1) ∧
      (forall {h0 h1 k : BHist},
        hsame (append (BHist.e1 h0) k) (append (BHist.e1 h1) k) -> hsame h0 h1) := by
  constructor
  · intro h0 h1 k same
    exact BHist.e0.inj (append_right_cancel (k := k) same)
  · intro h0 h1 k same
    exact BHist.e1.inj (append_right_cancel (k := k) same)

end BEDC.FKernel.Cont
