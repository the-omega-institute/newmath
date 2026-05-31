import BEDC.Derived.BoundedRealSequenceUp.TasteGate

namespace BEDC.Derived.BoundedRealSequenceUp.LocatedBoundHandoff

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem BoundedRealSequenceLocatedBound_handoff
    {S W Q R I H C P N sourceRead readbackRead sealRead boundRead locatedRead : BHist} :
    UnaryHistory S →
      UnaryHistory W →
        UnaryHistory Q →
          UnaryHistory R →
            UnaryHistory I →
              UnaryHistory H →
                Cont S W sourceRead →
                  Cont sourceRead Q readbackRead →
                    Cont readbackRead R sealRead →
                      Cont sealRead I boundRead →
                        Cont boundRead H locatedRead →
                          UnaryHistory sourceRead ∧ UnaryHistory readbackRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                              UnaryHistory locatedRead ∧
                                BHistCarrier.toEventFlow
                                    (BoundedRealSequenceUp.mk S W Q R I H C P N) =
                                  BoundedRealSequenceTasteGate_single_carrier_alignment_to_event_flow
                                    (BoundedRealSequenceUp.mk S W Q R I H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont BHistCarrier
  intro sourceUnary windowUnary readbackUnary realUnary intervalUnary transportUnary
    sourceRoute readbackRoute sealRoute boundRoute locatedRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed sourceReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary realUnary sealRoute
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed sealReadUnary intervalUnary boundRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed boundReadUnary transportUnary locatedRoute
  exact
    ⟨sourceReadUnary, readbackReadUnary, sealReadUnary, boundReadUnary, locatedReadUnary,
      rfl⟩

end BEDC.Derived.BoundedRealSequenceUp.LocatedBoundHandoff
