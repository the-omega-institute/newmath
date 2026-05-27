import BEDC.Derived.RealSequenceAlgebraUp.TasteGate

namespace BEDC.Derived.RealSequenceAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RealSequenceAlgebraLimitConsumer (x : RealSequenceAlgebraUp) :
    ∃ outputSeal : BHist,
      outputSeal ∈ realSequenceAlgebraFields x ∧
        SemanticNameCert
          (fun row : BHist => hsame row outputSeal ∧ row ∈ realSequenceAlgebraFields x)
          (fun row : BHist => row ∈ realSequenceAlgebraFields x)
          (fun row : BHist => hsame row outputSeal ∧ row ∈ realSequenceAlgebraFields x)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
      operation outputSeal transport replay provenance localCert =>
      have outputMember :
          outputSeal ∈
            realSequenceAlgebraFields
              (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight
                readbackLeft readbackRight dyadicLedger operation outputSeal transport replay
                provenance localCert) :=
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <| List.Mem.head _
      refine ⟨outputSeal, outputMember, ?_⟩
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact ⟨outputSeal, hsame_refl outputSeal, outputMember⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' same₁ same₂
        exact hsame_trans same₁ same₂
      · intro row row' same source
        cases same
        exact source
      · intro row source
        exact source.right
      · intro row source
        exact source

end BEDC.Derived.RealSequenceAlgebraUp
