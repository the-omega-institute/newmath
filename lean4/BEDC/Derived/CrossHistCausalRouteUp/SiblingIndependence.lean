import BEDC.Derived.CrossHistCausalRouteUp.TasteGate

namespace BEDC.Derived.CrossHistCausalRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem CrossHistCausalRouteCarrier_sibling_independence
    (x : CrossHistCausalRouteUp) :
    ∃ observerA observerB causalRows maxRate symmetryGate nonEscapeGate trace transport
      access provenance localName : BHist,
      crossHistCausalRouteFields x =
          [observerA, observerB, causalRows, maxRate, symmetryGate, nonEscapeGate,
            trace, transport, access, provenance, localName] ∧
        crossHistCausalRouteToEventFlow x =
          [[BMark.b0],
            crossHistCausalRouteEncodeBHist observerA,
            [BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist observerB,
            [BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist causalRows,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist maxRate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist symmetryGate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist nonEscapeGate,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b0],
            crossHistCausalRouteEncodeBHist trace,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist transport,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist access,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist provenance,
            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
              BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
            crossHistCausalRouteEncodeBHist localName] ∧
          List.Mem (crossHistCausalRouteEncodeBHist causalRows)
            (crossHistCausalRouteToEventFlow x) ∧
            List.Mem (crossHistCausalRouteEncodeBHist maxRate)
              (crossHistCausalRouteToEventFlow x) ∧
              List.Mem (crossHistCausalRouteEncodeBHist trace)
                (crossHistCausalRouteToEventFlow x) ∧
                crossHistCausalRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  cases x with
  | mk observerA observerB causalRows maxRate symmetryGate nonEscapeGate trace transport
      access provenance localName =>
      refine
        ⟨observerA, observerB, causalRows, maxRate, symmetryGate, nonEscapeGate,
          trace, transport, access, provenance, localName, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] (List.Mem.head _)
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] <|
                    List.Mem.tail (crossHistCausalRouteEncodeBHist causalRows) <|
                      List.Mem.tail [BMark.b1, BMark.b1, BMark.b1, BMark.b0]
                        (List.Mem.head _)
      · exact
          List.Mem.tail [BMark.b0] <|
            List.Mem.tail (crossHistCausalRouteEncodeBHist observerA) <|
              List.Mem.tail [BMark.b1, BMark.b0] <|
                List.Mem.tail (crossHistCausalRouteEncodeBHist observerB) <|
                  List.Mem.tail [BMark.b1, BMark.b1, BMark.b0] <|
                    List.Mem.tail (crossHistCausalRouteEncodeBHist causalRows) <|
                      List.Mem.tail [BMark.b1, BMark.b1, BMark.b1, BMark.b0] <|
                        List.Mem.tail (crossHistCausalRouteEncodeBHist maxRate) <|
                          List.Mem.tail
                            [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0] <|
                            List.Mem.tail
                              (crossHistCausalRouteEncodeBHist symmetryGate) <|
                              List.Mem.tail
                                [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                                  BMark.b0] <|
                                List.Mem.tail
                                  (crossHistCausalRouteEncodeBHist nonEscapeGate) <|
                                  List.Mem.tail
                                    [BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                                      BMark.b1, BMark.b1, BMark.b0]
                                    (List.Mem.head _)

end BEDC.Derived.CrossHistCausalRouteUp
