import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

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

def ComplexTermSeqCarrier (c : BHist -> BHist) : Prop :=
  forall n : BHist, UnaryHistory n -> ComplexHistoryCarrier (c n)

theorem ComplexTermSeqCarrier_hsame_transport {c d : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (c n) (d n)) ->
      ComplexTermSeqCarrier c -> ComplexTermSeqCarrier d := by
  intro pointwise carrier n unaryN
  cases carrier n unaryN with
  | intro real rest =>
      cases rest with
      | intro imag data =>
          cases data with
          | intro realCarrier rest =>
              cases rest with
              | intro imagCarrier cont =>
                  exact Exists.intro real
                    (Exists.intro imag
                      (And.intro realCarrier
                        (And.intro imagCarrier
                          (cont_result_hsame_transport cont (pointwise unaryN)))))

end BEDC.Derived.ComplexSeriesUp
