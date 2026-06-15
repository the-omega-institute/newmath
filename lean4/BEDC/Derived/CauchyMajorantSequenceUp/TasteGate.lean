import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMajorantSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMajorantSequenceUp : Type where
  | mk :
      (source modulus window dyadic majorant handoff realSeal transport replay
        localName : BHist) ->
        CauchyMajorantSequenceUp
  deriving DecidableEq

def cauchyMajorantSequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMajorantSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMajorantSequenceEncodeBHist h

def cauchyMajorantSequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMajorantSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMajorantSequenceDecodeBHist tail)

private theorem CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyMajorantSequenceFields : CauchyMajorantSequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMajorantSequenceUp.mk source modulus window dyadic majorant handoff realSeal
      transport replay localName =>
      [source, modulus, window, dyadic, majorant, handoff, realSeal, transport, replay,
        localName]

def cauchyMajorantSequenceToEventFlow : CauchyMajorantSequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMajorantSequenceFields x).map cauchyMajorantSequenceEncodeBHist

def cauchyMajorantSequenceFromEventFlow : EventFlow -> Option CauchyMajorantSequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | modulus :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | majorant :: rest4 =>
                      match rest4 with
                      | [] => none
                      | handoff :: rest5 =>
                          match rest5 with
                          | [] => none
                          | realSeal :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyMajorantSequenceUp.mk
                                                  (cauchyMajorantSequenceDecodeBHist source)
                                                  (cauchyMajorantSequenceDecodeBHist modulus)
                                                  (cauchyMajorantSequenceDecodeBHist window)
                                                  (cauchyMajorantSequenceDecodeBHist dyadic)
                                                  (cauchyMajorantSequenceDecodeBHist majorant)
                                                  (cauchyMajorantSequenceDecodeBHist handoff)
                                                  (cauchyMajorantSequenceDecodeBHist realSeal)
                                                  (cauchyMajorantSequenceDecodeBHist transport)
                                                  (cauchyMajorantSequenceDecodeBHist replay)
                                                  (cauchyMajorantSequenceDecodeBHist localName))
                                          | _ :: _ => none

private theorem CauchyMajorantSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyMajorantSequenceUp,
      cauchyMajorantSequenceFromEventFlow (cauchyMajorantSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source modulus window dyadic majorant handoff realSeal transport replay localName =>
      change
        some
          (CauchyMajorantSequenceUp.mk
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist source))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist modulus))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist window))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist dyadic))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist majorant))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist handoff))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist realSeal))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist transport))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist replay))
            (cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist localName))) =
          some
            (CauchyMajorantSequenceUp.mk source modulus window dyadic majorant handoff realSeal
              transport replay localName)
      rw [CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode source,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode modulus,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode window,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode dyadic,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode majorant,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode handoff,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyMajorantSequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMajorantSequenceUp} :
    cauchyMajorantSequenceToEventFlow x = cauchyMajorantSequenceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMajorantSequenceFromEventFlow (cauchyMajorantSequenceToEventFlow x) =
        cauchyMajorantSequenceFromEventFlow (cauchyMajorantSequenceToEventFlow y) :=
    congrArg cauchyMajorantSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyMajorantSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyMajorantSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyMajorantSequenceBHistCarrier : BHistCarrier CauchyMajorantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMajorantSequenceToEventFlow
  fromEventFlow := cauchyMajorantSequenceFromEventFlow

instance cauchyMajorantSequenceChapterTasteGate :
    ChapterTasteGate CauchyMajorantSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyMajorantSequenceTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyMajorantSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyMajorantSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyMajorantSequenceChapterTasteGate

namespace TasteGate

theorem CauchyMajorantSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyMajorantSequenceUp) ∧
        Nonempty (ChapterTasteGate CauchyMajorantSequenceUp) ∧
          cauchyMajorantSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro cauchyMajorantSequenceBHistCarrier,
      Nonempty.intro cauchyMajorantSequenceChapterTasteGate, rfl⟩

def taste_gate : ChapterTasteGate CauchyMajorantSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.CauchyMajorantSequenceUp.taste_gate

end TasteGate

theorem CauchyMajorantSequenceTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyMajorantSequenceDecodeBHist (cauchyMajorantSequenceEncodeBHist h) = h) /\
      (forall x : CauchyMajorantSequenceUp,
        cauchyMajorantSequenceFromEventFlow (cauchyMajorantSequenceToEventFlow x) = some x) /\
      (forall x y : CauchyMajorantSequenceUp,
        cauchyMajorantSequenceToEventFlow x = cauchyMajorantSequenceToEventFlow y -> x = y) /\
      cauchyMajorantSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyMajorantSequenceTasteGate_single_carrier_alignment_decode_encode,
      CauchyMajorantSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyMajorantSequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyMajorantSequenceUp
