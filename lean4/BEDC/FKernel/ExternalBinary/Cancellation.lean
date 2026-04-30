import BEDC.FKernel.ExternalBinary

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist

theorem external_append_cancel_hsame_nested_pair {a b c d : BWord} :
    hsame (append (append a c) d) (append (append b c) d) → hsame a b := by
  intro same
  have inner : hsame (append a c) (append b c) :=
    external_append_right_cancel_hsame
      (a := append a c) (b := append b c) (c := d) same
  exact external_append_right_cancel_hsame (a := a) (b := b) (c := c) inner

theorem external_append_cancel_three_context_hsame {a b l m r : BWord} :
    hsame (append (append l (append a m)) r) (append (append l (append b m)) r) →
      hsame a b := by
  intro same
  have withoutRight :
      hsame (append l (append a m)) (append l (append b m)) :=
    external_append_right_cancel_hsame
      (a := append l (append a m)) (b := append l (append b m)) (c := r) same
  have withoutLeft : hsame (append a m) (append b m) :=
    external_append_left_cancel_hsame (a := append a m) (b := append b m) (c := l)
      withoutRight
  exact external_append_right_cancel_hsame (a := a) (b := b) (c := m) withoutLeft

end BEDC.FKernel.ExternalBinary
