import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRecursorReplayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRecursorReplayUp : Type where
  | mk (I M B D R A H C P N : BHist) : BoundedRecursorReplayUp

def boundedRecursorReplayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRecursorReplayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRecursorReplayEncodeBHist h

def boundedRecursorReplayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRecursorReplayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRecursorReplayDecodeBHist tail)

private theorem boundedRecursorReplay_decode_encode_bhist :
    ∀ h : BHist,
      boundedRecursorReplayDecodeBHist
        (boundedRecursorReplayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundedRecursorReplayFields :
    BoundedRecursorReplayUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRecursorReplayUp.mk I M B D R A H C P N => [I, M, B, D, R, A, H, C, P, N]

def boundedRecursorReplayToEventFlow :
    BoundedRecursorReplayUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRecursorReplayUp.mk I M B D R A H C P N =>
      [boundedRecursorReplayEncodeBHist I,
        boundedRecursorReplayEncodeBHist M,
        boundedRecursorReplayEncodeBHist B,
        boundedRecursorReplayEncodeBHist D,
        boundedRecursorReplayEncodeBHist R,
        boundedRecursorReplayEncodeBHist A,
        boundedRecursorReplayEncodeBHist H,
        boundedRecursorReplayEncodeBHist C,
        boundedRecursorReplayEncodeBHist P,
        boundedRecursorReplayEncodeBHist N]

def boundedRecursorReplayFromEventFlow :
    EventFlow → Option BoundedRecursorReplayUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: M :: B :: D :: R :: A :: H :: C :: P :: N :: [] =>
      some
        (BoundedRecursorReplayUp.mk
          (boundedRecursorReplayDecodeBHist I)
          (boundedRecursorReplayDecodeBHist M)
          (boundedRecursorReplayDecodeBHist B)
          (boundedRecursorReplayDecodeBHist D)
          (boundedRecursorReplayDecodeBHist R)
          (boundedRecursorReplayDecodeBHist A)
          (boundedRecursorReplayDecodeBHist H)
          (boundedRecursorReplayDecodeBHist C)
          (boundedRecursorReplayDecodeBHist P)
          (boundedRecursorReplayDecodeBHist N))
  | _ => none

private theorem boundedRecursorReplay_round_trip :
    ∀ x : BoundedRecursorReplayUp,
      boundedRecursorReplayFromEventFlow
        (boundedRecursorReplayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M B D R A H C P N =>
      change
        some
            (BoundedRecursorReplayUp.mk
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist I))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist M))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist B))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist D))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist R))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist A))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist H))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist C))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist P))
              (boundedRecursorReplayDecodeBHist (boundedRecursorReplayEncodeBHist N))) =
          some (BoundedRecursorReplayUp.mk I M B D R A H C P N)
      rw [boundedRecursorReplay_decode_encode_bhist I,
        boundedRecursorReplay_decode_encode_bhist M,
        boundedRecursorReplay_decode_encode_bhist B,
        boundedRecursorReplay_decode_encode_bhist D,
        boundedRecursorReplay_decode_encode_bhist R,
        boundedRecursorReplay_decode_encode_bhist A,
        boundedRecursorReplay_decode_encode_bhist H,
        boundedRecursorReplay_decode_encode_bhist C,
        boundedRecursorReplay_decode_encode_bhist P,
        boundedRecursorReplay_decode_encode_bhist N]

private theorem boundedRecursorReplayToEventFlow_injective
    {x y : BoundedRecursorReplayUp}
    (h : boundedRecursorReplayToEventFlow x =
      boundedRecursorReplayToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      boundedRecursorReplayFromEventFlow (boundedRecursorReplayToEventFlow x) =
        boundedRecursorReplayFromEventFlow (boundedRecursorReplayToEventFlow y) :=
    congrArg boundedRecursorReplayFromEventFlow h
  exact Option.some.inj
    (Eq.trans (boundedRecursorReplay_round_trip x).symm
      (Eq.trans hread (boundedRecursorReplay_round_trip y)))

private theorem boundedRecursorReplay_fields_faithful :
    ∀ x y : BoundedRecursorReplayUp,
      boundedRecursorReplayFields x = boundedRecursorReplayFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I M B D R A H C P N =>
      cases y with
      | mk I' M' B' D' R' A' H' C' P' N' =>
          cases hfields
          rfl

instance boundedRecursorReplayBHistCarrier :
    BHistCarrier BoundedRecursorReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRecursorReplayToEventFlow
  fromEventFlow := boundedRecursorReplayFromEventFlow

instance boundedRecursorReplayChapterTasteGate :
    ChapterTasteGate BoundedRecursorReplayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedRecursorReplayFromEventFlow
        (boundedRecursorReplayToEventFlow x) = some x
    exact boundedRecursorReplay_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedRecursorReplayToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedRecursorReplayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRecursorReplayChapterTasteGate

theorem BoundedRecursorReplayTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedRecursorReplayDecodeBHist
        (boundedRecursorReplayEncodeBHist h) = h) ∧
      (∀ x y : BoundedRecursorReplayUp,
        boundedRecursorReplayFields x =
          boundedRecursorReplayFields y → x = y) ∧
          boundedRecursorReplayFields
              (BoundedRecursorReplayUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            boundedRecursorReplayEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              boundedRecursorReplayEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
                boundedRecursorReplayEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨boundedRecursorReplay_decode_encode_bhist,
    boundedRecursorReplay_fields_faithful,
    rfl, rfl, rfl, rfl⟩

end BEDC.Derived.BoundedRecursorReplayUp
