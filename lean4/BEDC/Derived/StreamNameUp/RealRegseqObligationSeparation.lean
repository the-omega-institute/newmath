import BEDC.Derived.StreamNameUp.PointwiseHandoff

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameRealRegseqObligationSeparation {s t : BHist -> BHist}
    {bundle : ProbeBundle BHist} {n windowRead sealRead : BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      InBundle n bundle ->
        UnaryHistory n ->
          UnaryHistory windowRead ->
            UnaryHistory sealRead ->
              Cont windowRead sealRead (append windowRead sealRead) ->
                RatHistoryClassifier (s n) (t n) ∧ UnaryHistory n ∧
                  UnaryHistory (append windowRead sealRead) ∧
                    hsame (append windowRead sealRead) (append windowRead sealRead) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont hsame UnaryHistory
  intro classifier member nUnary windowUnary sealUnary displayedRoute
  have selected : RatHistoryClassifier (s n) (t n) :=
    classifier n member nUnary
  have handoffUnary : UnaryHistory (append windowRead sealRead) :=
    unary_cont_closed windowUnary sealUnary displayedRoute
  exact ⟨selected, nUnary, handoffUnary, hsame_refl (append windowRead sealRead)⟩

end BEDC.Derived.StreamNameUp
