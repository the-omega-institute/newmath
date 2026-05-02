import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryClassifier_cross_absent_source_exclusion {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h k : BHist} :
    OptionHistoryClassifier source h k ->
      (source h -> hsame k BHist.Empty -> False) /\
        (source k -> hsame h BHist.Empty -> False) := by
  intro classifier
  cases classifier with
  | intro _carrierH rest =>
      cases rest with
      | intro _carrierK sameHK =>
          constructor
          · intro sourceH sameKEmpty
            exact sourceExcludesEmpty h sourceH (hsame_trans sameHK sameKEmpty)
          · intro sourceK sameHEmpty
            exact sourceExcludesEmpty k sourceK
              (hsame_trans (hsame_symm sameHK) sameHEmpty)

end BEDC.Derived.OptionUp
