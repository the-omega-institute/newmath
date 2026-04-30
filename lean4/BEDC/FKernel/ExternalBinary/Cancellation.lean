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

theorem external_append_cancel_hsame_triple_suffix {a b c d e : BWord} :
    hsame (append (append (append a c) d) e) (append (append (append b c) d) e) →
      hsame a b := by
  intro same
  have withoutSuffix : hsame (append (append a c) d) (append (append b c) d) :=
    external_append_right_cancel_hsame
      (a := append (append a c) d) (b := append (append b c) d) (c := e) same
  exact external_append_cancel_hsame_nested_pair withoutSuffix

theorem external_append_cancel_four_context_hsame {a b l m n r : BWord} :
    hsame (append (append l (append (append a m) n)) r)
        (append (append l (append (append b m) n)) r) →
      hsame a b := by
  intro same
  have withoutRight :
      hsame (append l (append (append a m) n))
        (append l (append (append b m) n)) :=
    external_append_right_cancel_hsame
      (a := append l (append (append a m) n))
      (b := append l (append (append b m) n)) (c := r) same
  have withoutLeft : hsame (append (append a m) n) (append (append b m) n) :=
    external_append_left_cancel_hsame
      (a := append (append a m) n) (b := append (append b m) n) (c := l)
      withoutRight
  have withoutN : hsame (append a m) (append b m) :=
    external_append_right_cancel_hsame (a := append a m) (b := append b m) (c := n)
      withoutLeft
  exact external_append_right_cancel_hsame (a := a) (b := b) (c := m) withoutN

theorem external_append_cancel_two_sided_hsame_symmetric {a b l r : BWord} :
    hsame (append (append l a) r) (append (append l b) r) → hsame b a := by
  intro same
  have forward : hsame a b :=
    external_append_cancel_common_context (a := a) (b := b) (l := l) (r := r) same
  exact hsame_symm forward

end BEDC.FKernel.ExternalBinary
