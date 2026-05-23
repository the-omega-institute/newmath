import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealComparisonUp : Type where
  | mk (L0 L1 W R0 R1 D0 D1 B A H C P N : BHist) : LocatedRealComparisonUp
  deriving DecidableEq

def locatedRealComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealComparisonEncodeBHist h

def locatedRealComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealComparisonDecodeBHist tail)

private theorem LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealComparisonToEventFlow : LocatedRealComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      [locatedRealComparisonEncodeBHist L0, locatedRealComparisonEncodeBHist L1,
        locatedRealComparisonEncodeBHist W, locatedRealComparisonEncodeBHist R0,
        locatedRealComparisonEncodeBHist R1, locatedRealComparisonEncodeBHist D0,
        locatedRealComparisonEncodeBHist D1, locatedRealComparisonEncodeBHist B,
        locatedRealComparisonEncodeBHist A, locatedRealComparisonEncodeBHist H,
        locatedRealComparisonEncodeBHist C, locatedRealComparisonEncodeBHist P,
        locatedRealComparisonEncodeBHist N]

def locatedRealComparisonFromEventFlow : EventFlow → Option LocatedRealComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | L0 :: rest =>
      match rest with
      | [] => none
      | L1 :: rest =>
          match rest with
          | [] => none
          | W :: rest =>
              match rest with
              | [] => none
              | R0 :: rest =>
                  match rest with
                  | [] => none
                  | R1 :: rest =>
                      match rest with
                      | [] => none
                      | D0 :: rest =>
                          match rest with
                          | [] => none
                          | D1 :: rest =>
                              match rest with
                              | [] => none
                              | B :: rest =>
                                  match rest with
                                  | [] => none
                                  | A :: rest =>
                                      match rest with
                                      | [] => none
                                      | H :: rest =>
                                          match rest with
                                          | [] => none
                                          | C :: rest =>
                                              match rest with
                                              | [] => none
                                              | P :: rest =>
                                                  match rest with
                                                  | [] => none
                                                  | N :: rest =>
                                                      match rest with
                                                      | [] =>
                                                          some
                                                            (LocatedRealComparisonUp.mk
                                                              (locatedRealComparisonDecodeBHist L0)
                                                              (locatedRealComparisonDecodeBHist L1)
                                                              (locatedRealComparisonDecodeBHist W)
                                                              (locatedRealComparisonDecodeBHist R0)
                                                              (locatedRealComparisonDecodeBHist R1)
                                                              (locatedRealComparisonDecodeBHist D0)
                                                              (locatedRealComparisonDecodeBHist D1)
                                                              (locatedRealComparisonDecodeBHist B)
                                                              (locatedRealComparisonDecodeBHist A)
                                                              (locatedRealComparisonDecodeBHist H)
                                                              (locatedRealComparisonDecodeBHist C)
                                                              (locatedRealComparisonDecodeBHist P)
                                                              (locatedRealComparisonDecodeBHist N))
                                                      | _ :: _ => none
  | [] => none

private theorem LocatedRealComparisonUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealComparisonUp,
      locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L0 L1 W R0 R1 D0 D1 B A H C P N =>
      change
        some
          (LocatedRealComparisonUp.mk
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist L0))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist L1))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist W))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist R0))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist R1))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist D0))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist D1))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist B))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist A))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist H))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist C))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist P))
            (locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist N))) =
          some (LocatedRealComparisonUp.mk L0 L1 W R0 R1 D0 D1 B A H C P N)
      rw [LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode L0,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode L1,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode W,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode R0,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode R1,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode D0,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode D1,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode B,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode A,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealComparisonUp} :
    locatedRealComparisonToEventFlow x = locatedRealComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) =
        locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow y) :=
    congrArg locatedRealComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealComparisonUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealComparisonUpTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealComparisonBHistCarrier : BHistCarrier LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealComparisonToEventFlow
  fromEventFlow := locatedRealComparisonFromEventFlow

instance locatedRealComparisonChapterTasteGate :
    ChapterTasteGate LocatedRealComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x
    exact LocatedRealComparisonUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedRealComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedRealComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealComparisonChapterTasteGate

theorem LocatedRealComparisonUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealComparisonDecodeBHist (locatedRealComparisonEncodeBHist h) = h) ∧
      (∀ x : LocatedRealComparisonUp,
        locatedRealComparisonFromEventFlow (locatedRealComparisonToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealComparisonUp,
        locatedRealComparisonToEventFlow x = locatedRealComparisonToEventFlow y → x = y) ∧
      locatedRealComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedRealComparisonUpTasteGate_single_carrier_alignment_decode_encode,
      LocatedRealComparisonUpTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedRealComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedRealComparisonUp
