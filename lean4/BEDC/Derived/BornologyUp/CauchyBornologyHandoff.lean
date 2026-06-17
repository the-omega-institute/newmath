import BEDC.Derived.BornologyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BornologyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BornologyCarrier_cauchy_bornology_handoff
    {F S U E D H C P N sourceRead unionRead cauchyRead : BHist} :
    BornologyTasteGate_single_carrier_alignment_fields (BornologyUp.mk F S U E D H C P N) =
        [F, S, U, E, D, H, C, P, N] →
      UnaryHistory F →
        UnaryHistory E →
          UnaryHistory U →
            UnaryHistory D →
              UnaryHistory N →
                Cont F E sourceRead →
                  Cont sourceRead U unionRead →
                    Cont unionRead D cauchyRead →
                      UnaryHistory sourceRead ∧ UnaryHistory unionRead ∧
                        UnaryHistory cauchyRead ∧ Cont F E sourceRead ∧
                          Cont sourceRead U unionRead ∧ Cont unionRead D cauchyRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro fieldRows fUnary eUnary uUnary dUnary _nUnary sourceRoute unionRoute cauchyRoute
  cases fieldRows
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed fUnary eUnary sourceRoute
  have unionUnary : UnaryHistory unionRead :=
    unary_cont_closed sourceUnary uUnary unionRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unionUnary dUnary cauchyRoute
  exact ⟨sourceUnary, unionUnary, cauchyUnary, sourceRoute, unionRoute, cauchyRoute⟩

end BEDC.Derived.BornologyUp
