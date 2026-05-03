import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

inductive ComplexPartSum (zero : BHist) (c : BHist -> BHist) : BHist -> BHist -> Prop where
  | zero : ComplexPartSum zero c BHist.Empty zero
  | step {n S T : BHist} :
      ComplexPartSum zero c n S -> Cont S (c n) T -> ComplexPartSum zero c (BHist.e1 n) T

theorem ComplexPartSum_deterministic {zero : BHist} {c : BHist -> BHist} {n S T : BHist} :
    ComplexPartSum zero c n S -> ComplexPartSum zero c n T -> hsame S T := by
  intro left
  induction left generalizing T with
  | zero =>
      intro right
      cases right with
      | zero =>
          exact hsame_refl zero
  | step leftSum leftStep ih =>
      intro right
      cases right with
      | step rightSum rightStep =>
          have samePartial := ih rightSum
          exact cont_respects_hsame samePartial (hsame_refl (c _)) leftStep rightStep

end BEDC.Derived.ComplexSeriesUp
