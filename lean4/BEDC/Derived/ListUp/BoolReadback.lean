import BEDC.Derived.BoolUp
import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_BoolHistoryClassifier_cons_mark_readback
    {h k : BEDC.FKernel.Hist.BHist} {xs ys : ListCarrier BEDC.FKernel.Hist.BHist} :
    ListClassifierSpec BEDC.Derived.BoolUp.BoolHistoryClassifier (h :: xs) (k :: ys) ->
      (exists v : BEDC.FKernel.Mark.BMark, exists w : BEDC.FKernel.Mark.BMark,
        BEDC.FKernel.Hist.hsame h (BEDC.Derived.BoolUp.BoolEndpoint v) /\
          BEDC.FKernel.Hist.hsame k (BEDC.Derived.BoolUp.BoolEndpoint w) /\
            BEDC.FKernel.Mark.msame v w) /\
        ListClassifierSpec BEDC.Derived.BoolUp.BoolHistoryClassifier xs ys := by
  intro classifier
  cases classifier with
  | intro headClassifier tailClassifier =>
      constructor
      · exact
          (BEDC.Derived.BoolUp.BoolHistoryClassifier_mark_readback_exactness
            (h := h) (k := k)).mp headClassifier
      · exact tailClassifier

end BEDC.Derived.ListUp
