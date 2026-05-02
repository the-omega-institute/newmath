import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionSourceExcludesEmpty_hsame_transport_absurd {source : BHist → Prop}
    (source_transport : ∀ {h k : BHist}, hsame h k → source h → source k)
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    source h → hsame h k → hsame k BHist.Empty → False := by
  intro sourceH sameHK sameKEmpty
  exact sourceExcludesEmpty k (source_transport sameHK sourceH) sameKEmpty

end BEDC.Derived.OptionUp
