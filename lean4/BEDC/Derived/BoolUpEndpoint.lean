import BEDC.Derived.BoolUp

namespace BEDC.Derived.BoolUp

theorem BoolHistoryClassifier_endpoint_exactness {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k ↔
      (BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty ∧
          BEDC.FKernel.Hist.hsame k BEDC.FKernel.Hist.BHist.Empty) ∨
        (BEDC.FKernel.Hist.hsame h
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) ∧
          BEDC.FKernel.Hist.hsame k
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty)) := by
  constructor
  · exact BoolHistoryClassifier_cases
  · intro endpoints
    cases endpoints with
    | inl emptyEndpoints =>
        constructor
        · exact Or.inl emptyEndpoints.left
        · constructor
          · exact Or.inl emptyEndpoints.right
          · exact BEDC.FKernel.Hist.hsame_trans emptyEndpoints.left
              (BEDC.FKernel.Hist.hsame_symm emptyEndpoints.right)
    | inr oneEndpoints =>
        constructor
        · exact Or.inr oneEndpoints.left
        · constructor
          · exact Or.inr oneEndpoints.right
          · exact BEDC.FKernel.Hist.hsame_trans oneEndpoints.left
              (BEDC.FKernel.Hist.hsame_symm oneEndpoints.right)

end BEDC.Derived.BoolUp
