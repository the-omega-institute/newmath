import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformPolygonalApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformPolygonalApproximationUp : Type where
  | mk (I M L Q F R D H C P N : BHist) : UniformPolygonalApproximationUp
  deriving DecidableEq

def uniformPolygonalApproximationFields :
    UniformPolygonalApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformPolygonalApproximationUp.mk I M L Q F R D H C P N =>
      [I, M, L, Q, F, R, D, H, C, P, N]

def uniformPolygonalApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformPolygonalApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformPolygonalApproximationEncodeBHist h

def uniformPolygonalApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformPolygonalApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformPolygonalApproximationDecodeBHist tail)

private theorem uniformPolygonalApproximation_decode_encode_bhist :
    ∀ h : BHist,
      uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformPolygonalApproximationToEventFlow :
    UniformPolygonalApproximationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformPolygonalApproximationFields x).map
    uniformPolygonalApproximationEncodeBHist

private def uniformPolygonalApproximationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformPolygonalApproximationEventAtDefault index rest

def uniformPolygonalApproximationFromEventFlow
    (ef : EventFlow) : Option UniformPolygonalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformPolygonalApproximationUp.mk
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 0 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 1 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 2 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 3 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 4 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 5 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 6 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 7 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 8 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 9 ef))
      (uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEventAtDefault 10 ef)))

private theorem uniformPolygonalApproximation_round_trip :
    ∀ x : UniformPolygonalApproximationUp,
      uniformPolygonalApproximationFromEventFlow
        (uniformPolygonalApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M L Q F R D H C P N =>
      change
        some
          (UniformPolygonalApproximationUp.mk
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist I))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist M))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist L))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist Q))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist F))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist R))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist D))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist H))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist C))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist P))
            (uniformPolygonalApproximationDecodeBHist
              (uniformPolygonalApproximationEncodeBHist N))) =
          some (UniformPolygonalApproximationUp.mk I M L Q F R D H C P N)
      rw [uniformPolygonalApproximation_decode_encode_bhist I,
        uniformPolygonalApproximation_decode_encode_bhist M,
        uniformPolygonalApproximation_decode_encode_bhist L,
        uniformPolygonalApproximation_decode_encode_bhist Q,
        uniformPolygonalApproximation_decode_encode_bhist F,
        uniformPolygonalApproximation_decode_encode_bhist R,
        uniformPolygonalApproximation_decode_encode_bhist D,
        uniformPolygonalApproximation_decode_encode_bhist H,
        uniformPolygonalApproximation_decode_encode_bhist C,
        uniformPolygonalApproximation_decode_encode_bhist P,
        uniformPolygonalApproximation_decode_encode_bhist N]

private theorem uniformPolygonalApproximationToEventFlow_injective
    {x y : UniformPolygonalApproximationUp} :
    uniformPolygonalApproximationToEventFlow x =
      uniformPolygonalApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformPolygonalApproximationFromEventFlow
          (uniformPolygonalApproximationToEventFlow x) =
        uniformPolygonalApproximationFromEventFlow
          (uniformPolygonalApproximationToEventFlow y) :=
    congrArg uniformPolygonalApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformPolygonalApproximation_round_trip x).symm
      (Eq.trans hread (uniformPolygonalApproximation_round_trip y)))

instance uniformPolygonalApproximationBHistCarrier :
    BHistCarrier UniformPolygonalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformPolygonalApproximationToEventFlow
  fromEventFlow := uniformPolygonalApproximationFromEventFlow

instance uniformPolygonalApproximationChapterTasteGate :
    ChapterTasteGate UniformPolygonalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformPolygonalApproximationFromEventFlow
          (uniformPolygonalApproximationToEventFlow x) =
        some x
    exact uniformPolygonalApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformPolygonalApproximationToEventFlow_injective heq)

instance uniformPolygonalApproximationFieldFaithful :
    FieldFaithful UniformPolygonalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformPolygonalApproximationFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk I M L Q F R D H C P N =>
      cases y with
      | mk I' M' L' Q' F' R' D' H' C' P' N' =>
          cases hfields
          rfl

def taste_gate : ChapterTasteGate UniformPolygonalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformPolygonalApproximationChapterTasteGate

theorem UniformPolygonalApproximationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      uniformPolygonalApproximationDecodeBHist
        (uniformPolygonalApproximationEncodeBHist h) = h) /\
      (forall x : UniformPolygonalApproximationUp,
        uniformPolygonalApproximationFromEventFlow
          (uniformPolygonalApproximationToEventFlow x) = some x) /\
      (forall x y : UniformPolygonalApproximationUp,
        uniformPolygonalApproximationToEventFlow x =
          uniformPolygonalApproximationToEventFlow y -> x = y) /\
      uniformPolygonalApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact uniformPolygonalApproximation_decode_encode_bhist
  · constructor
    · exact uniformPolygonalApproximation_round_trip
    · constructor
      · intro x y heq
        exact uniformPolygonalApproximationToEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformPolygonalApproximationUp
