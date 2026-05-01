import BEDC.FKernel.ExternalBinary

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist

theorem external_append_bit_result_cross_impossible :
    (forall {a b r b1 : BWord}, append a b = BHist.e0 r -> b = BHist.e1 b1 -> False) /\
      (forall {a b r b0 : BWord}, append a b = BHist.e1 r -> b = BHist.e0 b0 -> False) := by
  constructor
  · intro a b r b1 h hb
    cases hb
    cases h
  · intro a b r b0 h hb
    cases hb
    cases h

end BEDC.FKernel.ExternalBinary
