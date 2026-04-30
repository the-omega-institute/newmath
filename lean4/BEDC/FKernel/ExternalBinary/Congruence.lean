import BEDC.FKernel.ExternalBinary

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist

theorem external_append_hsame_congruence {a a' b b' : BWord} :
    hsame a a' → hsame b b' → hsame (append a b) (append a' b') := by
  intro ha hb
  cases ha
  cases hb
  exact hsame_refl (append a b)

end BEDC.FKernel.ExternalBinary
