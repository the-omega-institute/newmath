import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem StreamNameRealCompletionFourObjectExitRoute
    {stream dyadic regseq real support exit : BHist} {bundle : ProbeBundle BHist} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont stream dyadic support ->
              Cont regseq real exit ->
                InBundle stream bundle ->
                  InBundle dyadic bundle ->
                    InBundle regseq bundle ->
                      InBundle real bundle ->
                        UnaryHistory support ∧ UnaryHistory exit ∧
                          Cont stream dyadic support ∧ Cont regseq real exit ∧
                            InBundle stream bundle ∧ InBundle dyadic bundle ∧
                              InBundle regseq bundle ∧ InBundle real bundle := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont InBundle UnaryHistory
  intro streamUnary dyadicUnary regseqUnary realUnary supportRoute exitRoute streamMember
    dyadicMember regseqMember realMember
  have supportUnary : UnaryHistory support :=
    unary_cont_closed streamUnary dyadicUnary supportRoute
  have exitUnary : UnaryHistory exit :=
    unary_cont_closed regseqUnary realUnary exitRoute
  exact
    ⟨supportUnary, exitUnary, supportRoute, exitRoute, streamMember, dyadicMember,
      regseqMember, realMember⟩

end BEDC.Derived.StreamNameUp
