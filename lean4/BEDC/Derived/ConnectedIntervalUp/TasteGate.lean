import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConnectedIntervalUp : Type where
  | mk (L R W B S T E H C P N : BHist) : ConnectedIntervalUp
  deriving DecidableEq

def connectedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: connectedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: connectedIntervalEncodeBHist h

def connectedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (connectedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (connectedIntervalDecodeBHist tail)

private theorem connectedInterval_decode_encode :
    ∀ h : BHist, connectedIntervalDecodeBHist (connectedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def connectedIntervalFields : ConnectedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConnectedIntervalUp.mk L R W B S T E H C P N => [L, R, W, B, S, T, E, H, C, P, N]

def connectedIntervalToEventFlow : ConnectedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (connectedIntervalFields x).map connectedIntervalEncodeBHist

def connectedIntervalFromEventFlow : EventFlow → Option ConnectedIntervalUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: restL =>
      match restL with
      | R :: restR =>
          match restR with
          | W :: restW =>
              match restW with
              | B :: restB =>
                  match restB with
                  | S :: restS =>
                      match restS with
                      | T :: restT =>
                          match restT with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (ConnectedIntervalUp.mk
                                                      (connectedIntervalDecodeBHist L)
                                                      (connectedIntervalDecodeBHist R)
                                                      (connectedIntervalDecodeBHist W)
                                                      (connectedIntervalDecodeBHist B)
                                                      (connectedIntervalDecodeBHist S)
                                                      (connectedIntervalDecodeBHist T)
                                                      (connectedIntervalDecodeBHist E)
                                                      (connectedIntervalDecodeBHist H)
                                                      (connectedIntervalDecodeBHist C)
                                                      (connectedIntervalDecodeBHist P)
                                                      (connectedIntervalDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem connectedInterval_round_trip :
    ∀ x : ConnectedIntervalUp,
      connectedIntervalFromEventFlow (connectedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W B S T E H C P N =>
      change
        some
            (ConnectedIntervalUp.mk
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist L))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist R))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist W))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist B))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist S))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist T))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist E))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist H))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist C))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist P))
              (connectedIntervalDecodeBHist (connectedIntervalEncodeBHist N))) =
          some (ConnectedIntervalUp.mk L R W B S T E H C P N)
      rw [connectedInterval_decode_encode L]
      rw [connectedInterval_decode_encode R]
      rw [connectedInterval_decode_encode W]
      rw [connectedInterval_decode_encode B]
      rw [connectedInterval_decode_encode S]
      rw [connectedInterval_decode_encode T]
      rw [connectedInterval_decode_encode E]
      rw [connectedInterval_decode_encode H]
      rw [connectedInterval_decode_encode C]
      rw [connectedInterval_decode_encode P]
      rw [connectedInterval_decode_encode N]

private theorem connectedIntervalToEventFlow_injective {x y : ConnectedIntervalUp} :
    connectedIntervalToEventFlow x = connectedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      connectedIntervalFromEventFlow (connectedIntervalToEventFlow x) =
        connectedIntervalFromEventFlow (connectedIntervalToEventFlow y) :=
    congrArg connectedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (connectedInterval_round_trip x).symm
      (Eq.trans hread (connectedInterval_round_trip y)))

instance connectedIntervalBHistCarrier : BHistCarrier ConnectedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := connectedIntervalToEventFlow
  fromEventFlow := connectedIntervalFromEventFlow

instance connectedIntervalChapterTasteGate : ChapterTasteGate ConnectedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change connectedIntervalFromEventFlow (connectedIntervalToEventFlow x) = some x
    exact connectedInterval_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (connectedIntervalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ConnectedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  connectedIntervalChapterTasteGate

theorem ConnectedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, connectedIntervalDecodeBHist (connectedIntervalEncodeBHist h) = h) ∧
      (∀ x : ConnectedIntervalUp,
        connectedIntervalFromEventFlow (connectedIntervalToEventFlow x) = some x) ∧
      (∀ x y : ConnectedIntervalUp,
        connectedIntervalToEventFlow x = connectedIntervalToEventFlow y → x = y) ∧
      ∃ x : ConnectedIntervalUp,
        x =
          ConnectedIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
        connectedIntervalFromEventFlow (connectedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact connectedInterval_decode_encode
  constructor
  · intro x
    exact connectedInterval_round_trip x
  constructor
  · intro x y heq
    exact connectedIntervalToEventFlow_injective heq
  · let x :=
      ConnectedIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
    exact ⟨x, rfl, connectedInterval_round_trip x⟩

end BEDC.Derived.ConnectedIntervalUp
