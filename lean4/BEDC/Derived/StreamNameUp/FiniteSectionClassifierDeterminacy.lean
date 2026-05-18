import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameFiniteSectionClassifierDeterminacy
    {s t s' t' : BHist -> BHist}
    {window dyadic regseq real support pullback terminal : BHist}
    {bundle : ProbeBundle BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      RatStreamNameFiniteWindowClassifier s' t' bundle ->
        UnaryHistory window ->
          UnaryHistory dyadic ->
            UnaryHistory regseq ->
              UnaryHistory real ->
                Cont window dyadic support ->
                  Cont support regseq pullback ->
                    Cont pullback real terminal ->
                      InBundle window bundle ->
                        InBundle dyadic bundle ->
                          InBundle regseq bundle ->
                            InBundle real bundle ->
                              RatHistoryClassifier (s window) (t window) ∧
                                RatHistoryClassifier (s' window) (t' window) ∧
                                  RatHistoryClassifier (s real) (t real) ∧
                                    RatHistoryClassifier (s' real) (t' real) ∧
                                      UnaryHistory terminal ∧ hsame terminal terminal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont hsame UnaryHistory
  intro classified classified' windowUnary dyadicUnary regseqUnary realUnary
    windowDyadicSupport supportRegseqPullback pullbackRealTerminal windowMember dyadicMember
    regseqMember realMember
  have windowClassified : RatHistoryClassifier (s window) (t window) :=
    classified window windowMember windowUnary
  have windowClassified' : RatHistoryClassifier (s' window) (t' window) :=
    classified' window windowMember windowUnary
  have realClassified : RatHistoryClassifier (s real) (t real) :=
    classified real realMember realUnary
  have realClassified' : RatHistoryClassifier (s' real) (t' real) :=
    classified' real realMember realUnary
  have supportUnary : UnaryHistory support :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicSupport
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed supportUnary regseqUnary supportRegseqPullback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed pullbackUnary realUnary pullbackRealTerminal
  exact
    ⟨windowClassified,
      windowClassified',
      realClassified,
      realClassified',
      terminalUnary,
      hsame_refl terminal⟩

end BEDC.Derived.StreamNameUp
