import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetCompletionUp : Type where
  | mk :
      (admission limitNet neighbour separation sequentialReadback realSeal transport replay
        provenance localName : BHist) ->
        FrechetCompletionUp
  deriving DecidableEq

def frechetCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetCompletionEncodeBHist h

def frechetCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetCompletionDecodeBHist tail)

theorem FrechetCompletionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, frechetCompletionDecodeBHist (frechetCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def frechetCompletionFields : FrechetCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetCompletionUp.mk admission limitNet neighbour separation sequentialReadback realSeal
      transport replay provenance localName =>
      [admission, limitNet, neighbour, separation, sequentialReadback, realSeal, transport,
        replay, provenance, localName]

def frechetCompletionToEventFlow : FrechetCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetCompletionFields x).map frechetCompletionEncodeBHist

def frechetCompletionFromEventFlow : EventFlow -> Option FrechetCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | admission :: rest0 =>
      match rest0 with
      | [] => none
      | limitNet :: rest1 =>
          match rest1 with
          | [] => none
          | neighbour :: rest2 =>
              match rest2 with
              | [] => none
              | separation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | sequentialReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
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
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FrechetCompletionUp.mk
                                                  (frechetCompletionDecodeBHist admission)
                                                  (frechetCompletionDecodeBHist limitNet)
                                                  (frechetCompletionDecodeBHist neighbour)
                                                  (frechetCompletionDecodeBHist separation)
                                                  (frechetCompletionDecodeBHist sequentialReadback)
                                                  (frechetCompletionDecodeBHist realSeal)
                                                  (frechetCompletionDecodeBHist transport)
                                                  (frechetCompletionDecodeBHist replay)
                                                  (frechetCompletionDecodeBHist provenance)
                                                  (frechetCompletionDecodeBHist localName))
                                          | _ :: _ => none

theorem FrechetCompletionTasteGate_single_carrier_alignment_round_trip :
    forall x : FrechetCompletionUp,
      frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk admission limitNet neighbour separation sequentialReadback realSeal transport replay
      provenance localName =>
      change
        some
          (FrechetCompletionUp.mk
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist admission))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist limitNet))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist neighbour))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist separation))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist sequentialReadback))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist realSeal))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist transport))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist replay))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist provenance))
            (frechetCompletionDecodeBHist (frechetCompletionEncodeBHist localName))) =
          some
            (FrechetCompletionUp.mk admission limitNet neighbour separation sequentialReadback
              realSeal transport replay provenance localName)
      rw [FrechetCompletionTasteGate_single_carrier_alignment_decode_encode admission,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode limitNet,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode neighbour,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode separation,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode sequentialReadback,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode realSeal,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode transport,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode replay,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode provenance,
        FrechetCompletionTasteGate_single_carrier_alignment_decode_encode localName]

theorem FrechetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrechetCompletionUp} :
    frechetCompletionToEventFlow x = frechetCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) =
        frechetCompletionFromEventFlow (frechetCompletionToEventFlow y) :=
    congrArg frechetCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance frechetCompletionBHistCarrier : BHistCarrier FrechetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetCompletionToEventFlow
  fromEventFlow := frechetCompletionFromEventFlow

instance frechetCompletionChapterTasteGate : ChapterTasteGate FrechetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (FrechetCompletionTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def frechetCompletionTasteGate : ChapterTasteGate FrechetCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  frechetCompletionChapterTasteGate

theorem FrechetCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist, frechetCompletionDecodeBHist (frechetCompletionEncodeBHist h) = h) ∧
      (forall x : FrechetCompletionUp,
        frechetCompletionFromEventFlow (frechetCompletionToEventFlow x) = some x) ∧
        (forall x y : FrechetCompletionUp,
          frechetCompletionToEventFlow x = frechetCompletionToEventFlow y -> x = y) ∧
          frechetCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FrechetCompletionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact FrechetCompletionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FrechetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.FrechetCompletionUp
