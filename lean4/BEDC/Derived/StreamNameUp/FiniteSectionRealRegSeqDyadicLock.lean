import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem StreamNameFiniteSectionRealRegSeqDyadicLock
    {stream dyadic regseq real support pullback terminal realRead completionRead : BHist}
    {bundle : ProbeBundle BHist} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont support regseq pullback ->
                Cont pullback real terminal ->
                  Cont terminal real realRead ->
                    Cont realRead regseq completionRead ->
                      InBundle stream bundle ->
                        InBundle dyadic bundle ->
                          InBundle regseq bundle ->
                            InBundle real bundle ->
                              UnaryHistory support ∧ UnaryHistory pullback ∧
                                UnaryHistory terminal ∧ UnaryHistory realRead ∧
                                  UnaryHistory completionRead ∧ Cont stream dyadic support ∧
                                    Cont support regseq pullback ∧ Cont pullback real terminal ∧
                                      Cont terminal real realRead ∧
                                        Cont realRead regseq completionRead ∧
                                          InBundle stream bundle ∧ InBundle dyadic bundle ∧
                                            InBundle regseq bundle ∧ InBundle real bundle := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont InBundle UnaryHistory
  intro streamUnary dyadicUnary regseqUnary realUnary supportRoute pullbackRoute terminalRoute
    realReadRoute completionRoute streamMember dyadicMember regseqMember realMember
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary supportRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed supportUnary regseqUnary pullbackRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed pullbackUnary realUnary terminalRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed terminalUnary realUnary realReadRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary regseqUnary completionRoute
  exact
    ⟨supportUnary, pullbackUnary, terminalUnary, realReadUnary, completionUnary,
      supportRoute, pullbackRoute, terminalRoute, realReadRoute, completionRoute,
      streamMember, dyadicMember, regseqMember, realMember⟩

end BEDC.Derived.StreamNameUp
