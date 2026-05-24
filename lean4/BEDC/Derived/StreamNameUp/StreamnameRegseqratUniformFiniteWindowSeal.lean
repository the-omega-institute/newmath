import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamnameRegseqratUniformFiniteWindowSeal
    {s t : BHist -> BHist} {bundle : ProbeBundle BHist}
    {window regseq uniform sealRow route : BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      InBundle window bundle ->
        UnaryHistory window ->
          Cont window regseq uniform ->
            Cont uniform sealRow route ->
              UnaryHistory regseq ->
                UnaryHistory sealRow ->
                  RatHistoryClassifier (s window) (t window) ∧ UnaryHistory uniform ∧
                    UnaryHistory route ∧ Cont window regseq uniform ∧
                      Cont uniform sealRow route := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont UnaryHistory
  intro classified windowMember windowUnary windowRegseqUniform uniformSealRoute regseqUnary
    sealUnary
  have selectedClassifier : RatHistoryClassifier (s window) (t window) :=
    classified window windowMember windowUnary
  have uniformUnary : UnaryHistory uniform :=
    unary_cont_closed windowUnary regseqUnary windowRegseqUniform
  have routeUnary : UnaryHistory route :=
    unary_cont_closed uniformUnary sealUnary uniformSealRoute
  exact
    ⟨selectedClassifier, uniformUnary, routeUnary, windowRegseqUniform, uniformSealRoute⟩

end BEDC.Derived.StreamNameUp
