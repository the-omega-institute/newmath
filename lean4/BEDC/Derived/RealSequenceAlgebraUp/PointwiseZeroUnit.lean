import BEDC.Derived.RealSequenceAlgebraUp.TasteGate

namespace BEDC.Derived.RealSequenceAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RealSequenceAlgebraCarrier_pointwise_zero_unit
    {sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
      operation outputSeal transport replay provenance localCert : BHist} :
    sourceLeft ∈
        realSequenceAlgebraFields
          (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
            readbackRight dyadicLedger operation outputSeal transport replay provenance
            localCert) ∧
      sourceRight ∈
        realSequenceAlgebraFields
          (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
            readbackRight dyadicLedger operation outputSeal transport replay provenance
            localCert) ∧
      operation ∈
        realSequenceAlgebraFields
          (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
            readbackRight dyadicLedger operation outputSeal transport replay provenance
            localCert) ∧
      outputSeal ∈
        realSequenceAlgebraFields
          (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
            readbackRight dyadicLedger operation outputSeal transport replay provenance
            localCert) ∧
      SemanticNameCert
        (fun row : BHist =>
          hsame row outputSeal ∧
            row ∈
              realSequenceAlgebraFields
                (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight
                  readbackLeft readbackRight dyadicLedger operation outputSeal transport replay
                  provenance localCert))
        (fun row : BHist =>
          row ∈
            realSequenceAlgebraFields
              (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight
                readbackLeft readbackRight dyadicLedger operation outputSeal transport replay
                provenance localCert))
        (fun row : BHist =>
          hsame row outputSeal ∧
            row ∈
              realSequenceAlgebraFields
                (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight
                  readbackLeft readbackRight dyadicLedger operation outputSeal transport replay
                  provenance localCert))
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert RealSequenceAlgebraUp
  let packet :=
    RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
      readbackRight dyadicLedger operation outputSeal transport replay provenance localCert
  have sourceLeftMember : sourceLeft ∈ realSequenceAlgebraFields packet := by
    exact List.Mem.head _
  have sourceRightMember : sourceRight ∈ realSequenceAlgebraFields packet := by
    exact List.Mem.tail _ (List.Mem.head _)
  have operationMember : operation ∈ realSequenceAlgebraFields packet := by
    exact
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <| List.Mem.head _
  have outputMember : outputSeal ∈ realSequenceAlgebraFields packet := by
    exact
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <| List.Mem.head _
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row outputSeal ∧ row ∈ realSequenceAlgebraFields packet)
        (fun row : BHist => row ∈ realSequenceAlgebraFields packet)
        (fun row : BHist => hsame row outputSeal ∧ row ∈ realSequenceAlgebraFields packet)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro outputSeal ⟨hsame_refl outputSeal, outputMember⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨sourceLeftMember, sourceRightMember, operationMember, outputMember, cert⟩

end BEDC.Derived.RealSequenceAlgebraUp
