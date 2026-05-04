import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem PairFrame_empty_head_iff {u t : BHist} :
    hsame (PairFrame u t) (BHist.e0 t) ↔ hsame u BHist.Empty := by
  constructor
  · intro same
    cases u with
    | Empty =>
        change hsame (BHist.e0 t) (BHist.e0 t) at same
        rfl
    | e0 u =>
        change hsame (BHist.e1 (BHist.e0 (PairFrame u t))) (BHist.e0 t) at same
        exact False.elim (not_hsame_e1_e0 same)
    | e1 u =>
        change hsame (BHist.e1 (BHist.e1 (PairFrame u t))) (BHist.e0 t) at same
        exact False.elim (not_hsame_e1_e0 same)
  · intro same
    cases same
    rfl

end BEDC.Derived.ListUp
