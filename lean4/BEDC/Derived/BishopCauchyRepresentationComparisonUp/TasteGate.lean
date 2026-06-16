import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyRepresentationComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyRepresentationComparisonUp : Type where
  | mk (R B S Q D E H C P N : BHist) : BishopCauchyRepresentationComparisonUp
  deriving DecidableEq

def BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist h

def BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
          tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
          tail)

private theorem BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist h) =
          h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields :
    BishopCauchyRepresentationComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyRepresentationComparisonUp.mk R B S Q D E H C P N =>
      [R, B, S, Q, D, E, H, C, P, N]

def bishopCauchyRepresentationComparisonToEventFlow :
    BishopCauchyRepresentationComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields
          token).map
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist

private def bishopCauchyRepresentationComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopCauchyRepresentationComparisonEventAtDefault index rest

def bishopCauchyRepresentationComparisonFromEventFlow
    (ef : EventFlow) : Option BishopCauchyRepresentationComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyRepresentationComparisonUp.mk
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 0 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 1 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 2 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 3 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 4 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 5 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 6 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 7 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 8 ef))
      (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
        (bishopCauchyRepresentationComparisonEventAtDefault 9 ef)))

private theorem bishopCauchyRepresentationComparison_round_trip :
    ∀ token : BishopCauchyRepresentationComparisonUp,
      bishopCauchyRepresentationComparisonFromEventFlow
        (bishopCauchyRepresentationComparisonToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R B S Q D E H C P N =>
      change
        some
          (BishopCauchyRepresentationComparisonUp.mk
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                R))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                B))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                S))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                Q))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                D))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                E))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                H))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                C))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                P))
            (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
              (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
                N))) =
          some (BishopCauchyRepresentationComparisonUp.mk R B S Q D E H C P N)
      rw [BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode R,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode B,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode S,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode Q,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode D,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode E,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode H,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode C,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode P,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem bishopCauchyRepresentationComparisonToEventFlow_injective
    {x y : BishopCauchyRepresentationComparisonUp} :
    bishopCauchyRepresentationComparisonToEventFlow x =
      bishopCauchyRepresentationComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyRepresentationComparisonFromEventFlow
          (bishopCauchyRepresentationComparisonToEventFlow x) =
        bishopCauchyRepresentationComparisonFromEventFlow
          (bishopCauchyRepresentationComparisonToEventFlow y) :=
    congrArg bishopCauchyRepresentationComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCauchyRepresentationComparison_round_trip x).symm
      (Eq.trans hread (bishopCauchyRepresentationComparison_round_trip y)))

private theorem bishopCauchyRepresentationComparison_fields_faithful
    {x y : BishopCauchyRepresentationComparisonUp} :
    BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields x =
      BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk R1 B1 S1 Q1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 B2 S2 Q2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCauchyRepresentationComparisonBHistCarrier :
    BHistCarrier BishopCauchyRepresentationComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyRepresentationComparisonToEventFlow
  fromEventFlow := bishopCauchyRepresentationComparisonFromEventFlow

instance bishopCauchyRepresentationComparisonChapterTasteGate :
    ChapterTasteGate BishopCauchyRepresentationComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyRepresentationComparisonFromEventFlow
        (bishopCauchyRepresentationComparisonToEventFlow x) = some x
    exact bishopCauchyRepresentationComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCauchyRepresentationComparisonToEventFlow_injective heq)

instance bishopCauchyRepresentationComparisonFieldFaithful :
    FieldFaithful BishopCauchyRepresentationComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields
  field_faithful := by
    intro x y h
    exact bishopCauchyRepresentationComparison_fields_faithful h

def taste_gate : ChapterTasteGate BishopCauchyRepresentationComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyRepresentationComparisonChapterTasteGate

theorem BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment :
    (∀ R B S Q D E H C P N : BHist,
      BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_fields
          (BishopCauchyRepresentationComparisonUp.mk R B S Q D E H C P N) =
        [R, B, S, Q, D, E, H, C, P, N]) ∧
      (∀ h : BHist,
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decodeBHist
          (BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
            h) = h) ∧
        BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨(by
        intro R B S Q D E H C P N
        rfl),
      BishopCauchyRepresentationComparisonTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.BishopCauchyRepresentationComparisonUp
