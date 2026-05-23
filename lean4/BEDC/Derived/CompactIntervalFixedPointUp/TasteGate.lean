import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalFixedPointUp : Type where
  | mk (J G R B W Q E H C P N : BHist) : CompactIntervalFixedPointUp
  deriving DecidableEq

def compactIntervalFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalFixedPointEncodeBHist h

def compactIntervalFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalFixedPointDecodeBHist tail)

private theorem CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalFixedPointFields : CompactIntervalFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalFixedPointUp.mk J G R B W Q E H C P N =>
      [J, G, R, B, W, Q, E, H, C, P, N]

def compactIntervalFixedPointToEventFlow : CompactIntervalFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactIntervalFixedPointFields x).map compactIntervalFixedPointEncodeBHist

def compactIntervalFixedPointFromEventFlow :
    EventFlow → Option CompactIntervalFixedPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | J :: restJ =>
      match restJ with
      | G :: restG =>
          match restG with
          | R :: restR =>
              match restR with
              | B :: restB =>
                  match restB with
                  | W :: restW =>
                      match restW with
                      | Q :: restQ =>
                          match restQ with
                          | E :: restE =>
                              match restE with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (CompactIntervalFixedPointUp.mk
                                                      (compactIntervalFixedPointDecodeBHist J)
                                                      (compactIntervalFixedPointDecodeBHist G)
                                                      (compactIntervalFixedPointDecodeBHist R)
                                                      (compactIntervalFixedPointDecodeBHist B)
                                                      (compactIntervalFixedPointDecodeBHist W)
                                                      (compactIntervalFixedPointDecodeBHist Q)
                                                      (compactIntervalFixedPointDecodeBHist E)
                                                      (compactIntervalFixedPointDecodeBHist H)
                                                      (compactIntervalFixedPointDecodeBHist C)
                                                      (compactIntervalFixedPointDecodeBHist P)
                                                      (compactIntervalFixedPointDecodeBHist N))
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

private theorem CompactIntervalFixedPointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactIntervalFixedPointUp,
      compactIntervalFixedPointFromEventFlow (compactIntervalFixedPointToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J G R B W Q E H C P N =>
      change
        some
          (CompactIntervalFixedPointUp.mk
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist J))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist G))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist R))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist B))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist W))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist Q))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist E))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist H))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist C))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist P))
            (compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist N))) =
          some (CompactIntervalFixedPointUp.mk J G R B W Q E H C P N)
      rw [CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode J,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode G,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode R,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode B,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode W,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode Q,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode E,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode H,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode C,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode P,
        CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactIntervalFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactIntervalFixedPointUp} :
    compactIntervalFixedPointToEventFlow x = compactIntervalFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalFixedPointFromEventFlow (compactIntervalFixedPointToEventFlow x) =
        compactIntervalFixedPointFromEventFlow (compactIntervalFixedPointToEventFlow y) :=
    congrArg compactIntervalFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactIntervalFixedPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactIntervalFixedPointTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalFixedPointBHistCarrier :
    BHistCarrier CompactIntervalFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalFixedPointToEventFlow
  fromEventFlow := compactIntervalFixedPointFromEventFlow

instance compactIntervalFixedPointChapterTasteGate :
    ChapterTasteGate CompactIntervalFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactIntervalFixedPointFromEventFlow (compactIntervalFixedPointToEventFlow x) = some x
    exact CompactIntervalFixedPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactIntervalFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactIntervalFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalFixedPointChapterTasteGate

theorem CompactIntervalFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactIntervalFixedPointDecodeBHist (compactIntervalFixedPointEncodeBHist h) = h) ∧
      (∀ x : CompactIntervalFixedPointUp,
        compactIntervalFixedPointFromEventFlow (compactIntervalFixedPointToEventFlow x) =
          some x) ∧
      (∀ x y : CompactIntervalFixedPointUp,
        compactIntervalFixedPointToEventFlow x = compactIntervalFixedPointToEventFlow y →
          x = y) ∧
      compactIntervalFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompactIntervalFixedPointTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact CompactIntervalFixedPointTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CompactIntervalFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.CompactIntervalFixedPointUp
