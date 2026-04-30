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

end BEDC.FKernel.ExternalBinary
