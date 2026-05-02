import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_right_cancel_hsame_result {h h' k r r' : BHist} :
    Cont h k r -> Cont h' k r' -> hsame r r' -> hsame h h' := by
  intro left right same
  apply append_right_cancel (k := k)
  exact left.symm.trans (same.trans right)

theorem cont_hsame_transport {h h' k k' r r' : BHist} :
    hsame h h' → hsame k k' → hsame r r' → Cont h k r → Cont h' k' r' := by
  intro sameH sameK sameR hcont
  cases sameH
  cases sameK
  exact BEDC.FKernel.Cont.cont_result_hsame_transport hcont sameR

theorem cont_cancel_common_context {a b c d ab ad left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont a d ad -> Cont ad c right ->
      hsame left right -> hsame b d := by
  intro abDef leftDef adDef rightDef same
  cases abDef
  cases adDef
  have commonSuffix : hsame (append a b) (append a d) := by
    apply append_right_cancel (k := c)
    exact leftDef.symm.trans (same.trans rightDef)
  exact append_left_cancel (h := a) commonSuffix

theorem continuation_right_cancellation {h h' k r : BHist} :
    Cont h k r -> Cont h' k r -> hsame h h' := by
  intro left right
  exact cont_right_cancel left right

theorem cont_mutual_extension_hsame {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h -> hsame h k := by
  intro left right
  have cycle : Cont h (append leftTail rightTail) h := by
    exact right.trans
      ((congrArg (fun x => append x rightTail) left).trans
        (append_assoc h leftTail rightTail))
  have tailEmpty : hsame (append leftTail rightTail) BHist.Empty :=
    cont_right_unit_unique cycle
  have leftEmpty : leftTail = BHist.Empty := (append_eq_empty_iff.mp tailEmpty).left
  cases leftEmpty
  exact left.symm

theorem cont_mutual_extension_tails_empty {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h ->
      hsame leftTail BHist.Empty ∧ hsame rightTail BHist.Empty := by
  intro left right
  have cycle : Cont h (append leftTail rightTail) h := by
    exact right.trans
      ((congrArg (fun x => append x rightTail) left).trans
        (append_assoc h leftTail rightTail))
  have tailEmpty : hsame (append leftTail rightTail) BHist.Empty :=
    cont_right_unit_unique cycle
  exact append_eq_empty_iff.mp tailEmpty

theorem cont_self_extension_tail_absurd {h tail : BHist} :
    (Cont h (BHist.e0 tail) h -> False) ∧
      (Cont h (BHist.e1 tail) h -> False) := by
  constructor
  · intro hcont
    exact not_hsame_e0_empty (cont_right_unit_unique hcont)
  · intro hcont
    exact not_hsame_e1_empty (cont_right_unit_unique hcont)

theorem cont_mutual_extension_left_tail_absurd {h k leftTail rightTail : BHist} :
    (Cont h (BHist.e0 leftTail) k -> Cont k rightTail h -> False) ∧
      (Cont h (BHist.e1 leftTail) k -> Cont k rightTail h -> False) := by
  constructor
  · intro left right
    exact not_hsame_e0_empty (cont_mutual_extension_tails_empty left right).left
  · intro left right
    exact not_hsame_e1_empty (cont_mutual_extension_tails_empty left right).left

theorem cont_cancel_hsame_left_context {a a' b d r r' : BHist} :
    Cont a b r -> Cont a' d r' -> hsame a a' -> hsame r r' -> hsame b d := by
  intro left right sameContext sameResult
  cases sameContext
  cases sameResult
  exact cont_left_cancel left right

theorem cont_composite_tail_unique {h k r f g tail : BHist} :
    Cont h f k -> Cont k g r -> Cont h tail r -> hsame tail (append f g) := by
  intro left right direct
  have composite : Cont h (append f g) r := by
    cases left
    exact right.trans (append_assoc h f g)
  exact cont_left_cancel direct composite

theorem cont_composite_left_factor {a b c f g fg : BHist} :
    Cont b g c -> Cont f g fg -> Cont a fg c -> Cont a f b := by
  intro right composite displayed
  have displayedWithCommonSuffix : Cont (append a f) g c := by
    cases composite
    exact cont_intro (displayed.trans (append_assoc a f g).symm)
  have sameMiddle : hsame (append a f) b :=
    cont_right_cancel displayedWithCommonSuffix right
  exact cont_result_hsame_transport (cont_intro rfl) sameMiddle

theorem cont_composite_right_factor {a b c f g fg : BHist} :
    Cont a f b -> Cont f g fg -> Cont a fg c -> Cont b g c := by
  intro left composite displayed
  cases left
  cases composite
  cases displayed
  exact cont_intro (append_assoc a f g).symm

theorem cont_prefix_iff {p a b f : BHist} :
    Cont (append p a) f (append p b) ↔ Cont a f b := by
  constructor
  · intro prefixed
    exact cont_prefix_cancel prefixed
  · intro base
    exact cont_intro ((congrArg (append p) base).trans (append_assoc p a f).symm)

theorem cont_suffix_iff {a b f p : BHist} :
    Cont a (append f p) (append b p) ↔ Cont a f b := by
  constructor
  · intro suffixed
    apply cont_intro
    apply append_right_cancel (k := p)
    exact suffixed.trans (append_assoc a f p).symm
  · intro base
    apply cont_intro
    cases base
    exact append_assoc a f p

end BEDC.FKernel.Cont
