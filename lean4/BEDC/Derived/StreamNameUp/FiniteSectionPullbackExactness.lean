import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem StreamNameFiniteSectionPullbackExactness
    {s t : BHist -> BHist} {stream dyadic regseq real support pullback terminal : BHist}
    {bundle : ProbeBundle BHist} :
    RatStreamNameFiniteWindowClassifier s t bundle ->
      UnaryHistory stream -> UnaryHistory dyadic -> UnaryHistory regseq -> UnaryHistory real ->
        Cont stream dyadic support -> Cont support regseq pullback ->
          Cont pullback real terminal -> InBundle stream bundle -> InBundle dyadic bundle ->
            InBundle regseq bundle -> InBundle real bundle ->
              RatHistoryClassifier (s stream) (t stream) ∧
                RatHistoryClassifier (s dyadic) (t dyadic) ∧
                  RatHistoryClassifier (s regseq) (t regseq) ∧
                    RatHistoryClassifier (s real) (t real) ∧ UnaryHistory support ∧
                      UnaryHistory pullback ∧ UnaryHistory terminal ∧
                        Cont stream dyadic support ∧ Cont support regseq pullback ∧
                          Cont pullback real terminal ∧ InBundle stream bundle ∧
                            InBundle dyadic bundle ∧ InBundle regseq bundle ∧
                              InBundle real bundle := by
  -- BEDC touchpoint anchor: BHist ProbeBundle InBundle Cont UnaryHistory
  intro classified streamUnary dyadicUnary regseqUnary realUnary streamDyadicSupport
    supportRegseqPullback pullbackRealTerminal streamMember dyadicMember regseqMember
    realMember
  have streamClassified : RatHistoryClassifier (s stream) (t stream) :=
    classified stream streamMember streamUnary
  have dyadicClassified : RatHistoryClassifier (s dyadic) (t dyadic) :=
    classified dyadic dyadicMember dyadicUnary
  have regseqClassified : RatHistoryClassifier (s regseq) (t regseq) :=
    classified regseq regseqMember regseqUnary
  have realClassified : RatHistoryClassifier (s real) (t real) :=
    classified real realMember realUnary
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSupport
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed supportUnary regseqUnary supportRegseqPullback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed pullbackUnary realUnary pullbackRealTerminal
  exact
    ⟨streamClassified,
      dyadicClassified,
      regseqClassified,
      realClassified,
      supportUnary,
      pullbackUnary,
      terminalUnary,
      streamDyadicSupport,
      supportRegseqPullback,
      pullbackRealTerminal,
      streamMember,
      dyadicMember,
      regseqMember,
      realMember⟩

end BEDC.Derived.StreamNameUp
