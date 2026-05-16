import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem StreamNameRegseqratRealDyadicWindowPullback
    {stream dyadic regseq real support pullback terminal : BHist}
    {bundle : ProbeBundle BHist} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont support regseq pullback ->
                Cont pullback real terminal ->
                  InBundle stream bundle ->
                    InBundle dyadic bundle ->
                      InBundle regseq bundle ->
                        InBundle real bundle ->
                          UnaryHistory support ∧ UnaryHistory pullback ∧
                            UnaryHistory terminal ∧ Cont stream dyadic support ∧
                              Cont support regseq pullback ∧ Cont pullback real terminal ∧
                                InBundle stream bundle ∧ InBundle dyadic bundle ∧
                                  InBundle regseq bundle ∧ InBundle real bundle := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont InBundle UnaryHistory
  intro streamUnary dyadicUnary regseqUnary realUnary streamDyadicSupport
    supportRegseqPullback pullbackRealTerminal streamMember dyadicMember regseqMember
    realMember
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicSupport
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed supportUnary regseqUnary supportRegseqPullback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed pullbackUnary realUnary pullbackRealTerminal
  exact
    ⟨supportUnary, pullbackUnary, terminalUnary, streamDyadicSupport,
      supportRegseqPullback, pullbackRealTerminal, streamMember, dyadicMember, regseqMember,
      realMember⟩

end BEDC.Derived.StreamNameUp
