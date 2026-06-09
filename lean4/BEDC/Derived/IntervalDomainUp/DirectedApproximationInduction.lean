import BEDC.Derived.IntervalDomainUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem IntervalDomainDirectedApproximationInduction
    {L R N W Q E H C P A firstRefinement laterRefinement streamRead regseqRead sealRead
      namedRead : BHist} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory N →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory E →
                UnaryHistory A →
                  Cont L R firstRefinement →
                    Cont firstRefinement N laterRefinement →
                      Cont W Q streamRead →
                        Cont laterRefinement streamRead regseqRead →
                          Cont regseqRead E sealRead →
                            Cont sealRead A namedRead →
                              hsame H (append C P) →
                                IntervalDomainTasteGate_single_carrier_alignment_fields
                                    (IntervalDomainUp.mk L R N W Q E H C P A) =
                                  [L, R, N, W, Q, E, H, C, P, A] ∧
                                  UnaryHistory firstRefinement ∧
                                    UnaryHistory laterRefinement ∧ UnaryHistory streamRead ∧
                                      UnaryHistory regseqRead ∧ UnaryHistory sealRead ∧
                                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory append
  intro leftUnary rightUnary nestedUnary streamUnary regseqUnary realSealUnary nameUnary
    firstRoute laterRoute streamRoute regseqRoute sealRoute namedRoute _historyRoute
  have firstUnary : UnaryHistory firstRefinement :=
    unary_cont_closed leftUnary rightUnary firstRoute
  have laterUnary : UnaryHistory laterRefinement :=
    unary_cont_closed firstUnary nestedUnary laterRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary regseqUnary streamRoute
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed laterUnary streamReadUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqReadUnary realSealUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nameUnary namedRoute
  exact ⟨rfl, firstUnary, laterUnary, streamReadUnary, regseqReadUnary, sealUnary, namedUnary⟩

end BEDC.Derived.IntervalDomainUp
