import BEDC.Derived.RealSequenceAlgebraUp.TasteGate

namespace BEDC.Derived.RealSequenceAlgebraUp

open BEDC.FKernel.Hist

theorem RealSequenceAlgebraCarrier_operation_row_exactness
    {sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
      operation outputSeal transport replay provenance localCert : BHist} :
    realSequenceAlgebraFields
        (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
          readbackRight dyadicLedger operation outputSeal transport replay provenance
          localCert) =
        [sourceLeft, sourceRight, windowLeft, windowRight, readbackLeft, readbackRight,
          dyadicLedger, operation, outputSeal, transport, replay, provenance, localCert] ∧
      operation ∈
        realSequenceAlgebraFields
          (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
            readbackRight dyadicLedger operation outputSeal transport replay provenance
            localCert) ∧
        outputSeal ∈
          realSequenceAlgebraFields
            (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
              readbackRight dyadicLedger operation outputSeal transport replay provenance
              localCert) := by
  -- BEDC touchpoint anchor: BHist hsame RealSequenceAlgebraUp
  constructor
  · rfl
  · constructor
    · exact
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <| List.Mem.head _
    · exact
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <| List.Mem.head _

end BEDC.Derived.RealSequenceAlgebraUp
