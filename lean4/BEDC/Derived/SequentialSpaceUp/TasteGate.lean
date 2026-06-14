import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialSpaceUp : Type where
  | mk :
      (index window limitRow topology comparison endpoint transport replay provenance nameCert :
        BHist) ->
      SequentialSpaceUp
  deriving DecidableEq

def sequentialSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialSpaceEncodeBHist h

def sequentialSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialSpaceDecodeBHist tail)

private theorem SequentialSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialSpaceFields : SequentialSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialSpaceUp.mk index window limitRow topology comparison endpoint transport replay
      provenance nameCert =>
      [index, window, limitRow, topology, comparison, endpoint, transport, replay, provenance,
        nameCert]

def sequentialSpaceToEventFlow : SequentialSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sequentialSpaceFields x).map sequentialSpaceEncodeBHist

def sequentialSpaceFromEventFlow : EventFlow -> Option SequentialSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | index :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | limitRow :: rest2 =>
              match rest2 with
              | [] => none
              | topology :: rest3 =>
                  match rest3 with
                  | [] => none
                  | comparison :: rest4 =>
                      match rest4 with
                      | [] => none
                      | endpoint :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (SequentialSpaceUp.mk
                                                  (sequentialSpaceDecodeBHist index)
                                                  (sequentialSpaceDecodeBHist window)
                                                  (sequentialSpaceDecodeBHist limitRow)
                                                  (sequentialSpaceDecodeBHist topology)
                                                  (sequentialSpaceDecodeBHist comparison)
                                                  (sequentialSpaceDecodeBHist endpoint)
                                                  (sequentialSpaceDecodeBHist transport)
                                                  (sequentialSpaceDecodeBHist replay)
                                                  (sequentialSpaceDecodeBHist provenance)
                                                  (sequentialSpaceDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem SequentialSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SequentialSpaceUp,
      sequentialSpaceFromEventFlow (sequentialSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk index window limitRow topology comparison endpoint transport replay provenance nameCert =>
      change
        some
          (SequentialSpaceUp.mk
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist index))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist window))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist limitRow))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist topology))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist comparison))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist endpoint))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist transport))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist replay))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist provenance))
            (sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist nameCert))) =
          some
            (SequentialSpaceUp.mk index window limitRow topology comparison endpoint transport
              replay provenance nameCert)
      rw [SequentialSpaceTasteGate_single_carrier_alignment_decode_encode index,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode window,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode limitRow,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode topology,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode comparison,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode endpoint,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode transport,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode replay,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode provenance,
        SequentialSpaceTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem SequentialSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SequentialSpaceUp} :
    sequentialSpaceToEventFlow x = sequentialSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialSpaceFromEventFlow (sequentialSpaceToEventFlow x) =
        sequentialSpaceFromEventFlow (sequentialSpaceToEventFlow y) :=
    congrArg sequentialSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SequentialSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SequentialSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SequentialSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SequentialSpaceUp, sequentialSpaceFields x = sequentialSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk index₁ window₁ limitRow₁ topology₁ comparison₁ endpoint₁ transport₁ replay₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk index₂ window₂ limitRow₂ topology₂ comparison₂ endpoint₂ transport₂ replay₂
          provenance₂ nameCert₂ =>
          injection hfields with hIndex tail0
          injection tail0 with hWindow tail1
          injection tail1 with hLimitRow tail2
          injection tail2 with hTopology tail3
          injection tail3 with hComparison tail4
          injection tail4 with hEndpoint tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hNameCert _
          subst hIndex
          subst hWindow
          subst hLimitRow
          subst hTopology
          subst hComparison
          subst hEndpoint
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hNameCert
          rfl

instance sequentialSpaceBHistCarrier : BHistCarrier SequentialSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialSpaceToEventFlow
  fromEventFlow := sequentialSpaceFromEventFlow

instance sequentialSpaceChapterTasteGate : ChapterTasteGate SequentialSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialSpaceFromEventFlow (sequentialSpaceToEventFlow x) = some x
    exact SequentialSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SequentialSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sequentialSpaceFieldFaithful : FieldFaithful SequentialSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialSpaceFields
  field_faithful := SequentialSpaceTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate SequentialSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialSpaceChapterTasteGate

theorem SequentialSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, sequentialSpaceDecodeBHist (sequentialSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SequentialSpaceUp) ∧
        Nonempty (ChapterTasteGate SequentialSpaceUp) ∧
          sequentialSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate FieldFaithful
  exact
    ⟨SequentialSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨sequentialSpaceBHistCarrier⟩, ⟨sequentialSpaceChapterTasteGate⟩, rfl⟩

end BEDC.Derived.SequentialSpaceUp
