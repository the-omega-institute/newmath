import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedRealCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedRealCompletenessUp : Type where
  | mk (S W R D L E H C P N : BHist) : BishopLocatedRealCompletenessUp
  deriving DecidableEq

def bishopLocatedRealCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRealCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRealCompletenessEncodeBHist h

def bishopLocatedRealCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRealCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRealCompletenessDecodeBHist tail)

private theorem BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedRealCompletenessFields :
    BishopLocatedRealCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRealCompletenessUp.mk S W R D L E H C P N =>
      [S, W, R, D, L, E, H, C, P, N]

def bishopLocatedRealCompletenessToEventFlow :
    BishopLocatedRealCompletenessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedRealCompletenessFields x).map
    bishopLocatedRealCompletenessEncodeBHist

private def bishopLocatedRealCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedRealCompletenessEventAtDefault index rest

def bishopLocatedRealCompletenessFromEventFlow
    (ef : EventFlow) : Option BishopLocatedRealCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedRealCompletenessUp.mk
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 0 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 1 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 2 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 3 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 4 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 5 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 6 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 7 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 8 ef))
      (bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEventAtDefault 9 ef)))

private theorem BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedRealCompletenessUp,
      bishopLocatedRealCompletenessFromEventFlow
        (bishopLocatedRealCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S W R D L E H C P N =>
      change
        some
          (BishopLocatedRealCompletenessUp.mk
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist S))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist W))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist R))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist D))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist L))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist E))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist H))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist C))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist P))
            (bishopLocatedRealCompletenessDecodeBHist
              (bishopLocatedRealCompletenessEncodeBHist N))) =
          some (BishopLocatedRealCompletenessUp.mk S W R D L E H C P N)
      rw [BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode S,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode W,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode R,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode D,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode L,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode E,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode H,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode C,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode P,
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedRealCompletenessUp} :
    bishopLocatedRealCompletenessToEventFlow x =
      bishopLocatedRealCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedRealCompletenessFromEventFlow
          (bishopLocatedRealCompletenessToEventFlow x) =
        bishopLocatedRealCompletenessFromEventFlow
          (bishopLocatedRealCompletenessToEventFlow y) :=
    congrArg bishopLocatedRealCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopLocatedRealCompletenessUp,
      bishopLocatedRealCompletenessFields x =
        bishopLocatedRealCompletenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 R1 D1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 R2 D2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedRealCompletenessBHistCarrier :
    BHistCarrier BishopLocatedRealCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedRealCompletenessToEventFlow
  fromEventFlow := bishopLocatedRealCompletenessFromEventFlow

instance bishopLocatedRealCompletenessChapterTasteGate :
    ChapterTasteGate BishopLocatedRealCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedRealCompletenessFromEventFlow
        (bishopLocatedRealCompletenessToEventFlow x) = some x
    exact BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_injective heq)

instance bishopLocatedRealCompletenessFieldFaithful :
    FieldFaithful BishopLocatedRealCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedRealCompletenessFields
  field_faithful :=
    BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate BishopLocatedRealCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedRealCompletenessChapterTasteGate

theorem BishopLocatedRealCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedRealCompletenessDecodeBHist
        (bishopLocatedRealCompletenessEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedRealCompletenessUp,
        bishopLocatedRealCompletenessFromEventFlow
          (bishopLocatedRealCompletenessToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedRealCompletenessUp,
          bishopLocatedRealCompletenessToEventFlow x =
            bishopLocatedRealCompletenessToEventFlow y → x = y) ∧
          bishopLocatedRealCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_decode,
      BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_round_trip,
      fun _x _y heq =>
        BishopLocatedRealCompletenessTasteGate_single_carrier_alignment_injective heq,
      rfl⟩

end BEDC.Derived.BishopLocatedRealCompletenessUp
