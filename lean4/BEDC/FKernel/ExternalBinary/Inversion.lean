import BEDC.FKernel.ExternalBinary

namespace BEDC.FKernel.ExternalBinary

open BEDC.FKernel.Hist

theorem external_append_bit_result_cases_by_right_word :
    (∀ {a r : BWord}, append a BHist.Empty = BHist.e0 r → a = BHist.e0 r) ∧
      (∀ {a b r : BWord}, append a (BHist.e0 b) = BHist.e0 r → append a b = r) ∧
      (∀ {a r : BWord}, append a BHist.Empty = BHist.e1 r → a = BHist.e1 r) ∧
      (∀ {a b r : BWord}, append a (BHist.e1 b) = BHist.e1 r → append a b = r) := by
  constructor
  · intro a r h
    exact h
  · constructor
    · intro a b r h
      exact BHist.e0.inj h
    · constructor
      · intro a r h
        exact h
      · intro a b r h
        exact BHist.e1.inj h

end BEDC.FKernel.ExternalBinary
