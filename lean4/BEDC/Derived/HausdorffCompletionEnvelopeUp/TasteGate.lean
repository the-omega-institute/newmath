import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionEnvelopeUp : Type where
  | mk (H S M W D R L T K P N : BHist) : HausdorffCompletionEnvelopeUp
  deriving DecidableEq

def hausdorffCompletionEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionEnvelopeEncodeBHist h

def hausdorffCompletionEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionEnvelopeDecodeBHist tail)

private theorem hausdorffCompletionEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionEnvelopeFields : HausdorffCompletionEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionEnvelopeUp.mk H S M W D R L T K P N =>
      [H, S, M, W, D, R, L, T, K, P, N]

def hausdorffCompletionEnvelopeToEventFlow : HausdorffCompletionEnvelopeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hausdorffCompletionEnvelopeFields x).map hausdorffCompletionEnvelopeEncodeBHist

private def hausdorffCompletionEnvelopeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionEnvelopeEventAtDefault index rest

def hausdorffCompletionEnvelopeFromEventFlow
    (ef : EventFlow) : Option HausdorffCompletionEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffCompletionEnvelopeUp.mk
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 0 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 1 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 2 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 3 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 4 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 5 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 6 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 7 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 8 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 9 ef))
      (hausdorffCompletionEnvelopeDecodeBHist
        (hausdorffCompletionEnvelopeEventAtDefault 10 ef)))

private theorem hausdorffCompletionEnvelope_round_trip :
    ∀ x : HausdorffCompletionEnvelopeUp,
      hausdorffCompletionEnvelopeFromEventFlow
        (hausdorffCompletionEnvelopeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H S M W D R L T K P N =>
      change
        some
          (HausdorffCompletionEnvelopeUp.mk
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist H))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist S))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist M))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist W))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist D))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist R))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist L))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist T))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist K))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist P))
            (hausdorffCompletionEnvelopeDecodeBHist
              (hausdorffCompletionEnvelopeEncodeBHist N))) =
          some (HausdorffCompletionEnvelopeUp.mk H S M W D R L T K P N)
      rw [hausdorffCompletionEnvelope_decode_encode_bhist H,
        hausdorffCompletionEnvelope_decode_encode_bhist S,
        hausdorffCompletionEnvelope_decode_encode_bhist M,
        hausdorffCompletionEnvelope_decode_encode_bhist W,
        hausdorffCompletionEnvelope_decode_encode_bhist D,
        hausdorffCompletionEnvelope_decode_encode_bhist R,
        hausdorffCompletionEnvelope_decode_encode_bhist L,
        hausdorffCompletionEnvelope_decode_encode_bhist T,
        hausdorffCompletionEnvelope_decode_encode_bhist K,
        hausdorffCompletionEnvelope_decode_encode_bhist P,
        hausdorffCompletionEnvelope_decode_encode_bhist N]

private theorem hausdorffCompletionEnvelopeToEventFlow_injective
    {x y : HausdorffCompletionEnvelopeUp} :
    hausdorffCompletionEnvelopeToEventFlow x =
      hausdorffCompletionEnvelopeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionEnvelopeFromEventFlow
          (hausdorffCompletionEnvelopeToEventFlow x) =
        hausdorffCompletionEnvelopeFromEventFlow
          (hausdorffCompletionEnvelopeToEventFlow y) :=
    congrArg hausdorffCompletionEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hausdorffCompletionEnvelope_round_trip x).symm
      (Eq.trans hread (hausdorffCompletionEnvelope_round_trip y)))

private theorem hausdorffCompletionEnvelope_field_faithful :
    ∀ x y : HausdorffCompletionEnvelopeUp,
      hausdorffCompletionEnvelopeFields x = hausdorffCompletionEnvelopeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H S M W D R L T K P N =>
      cases y with
      | mk H' S' M' W' D' R' L' T' K' P' N' =>
          cases hfields
          rfl

instance hausdorffCompletionEnvelopeBHistCarrier :
    BHistCarrier HausdorffCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionEnvelopeToEventFlow
  fromEventFlow := hausdorffCompletionEnvelopeFromEventFlow

instance hausdorffCompletionEnvelopeChapterTasteGate :
    ChapterTasteGate HausdorffCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionEnvelopeFromEventFlow
        (hausdorffCompletionEnvelopeToEventFlow x) = some x
    exact hausdorffCompletionEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffCompletionEnvelopeToEventFlow_injective heq)

instance hausdorffCompletionEnvelopeFieldFaithful :
    FieldFaithful HausdorffCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffCompletionEnvelopeFields
  field_faithful := hausdorffCompletionEnvelope_field_faithful

instance hausdorffCompletionEnvelopeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HausdorffCompletionEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffCompletionEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffCompletionEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffCompletionEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffCompletionEnvelopeChapterTasteGate

theorem HausdorffCompletionEnvelopeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HausdorffCompletionEnvelopeUp) ∧
      Nonempty (FieldFaithful HausdorffCompletionEnvelopeUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial HausdorffCompletionEnvelopeUp) ∧
      (∀ h : BHist,
        hausdorffCompletionEnvelopeDecodeBHist
          (hausdorffCompletionEnvelopeEncodeBHist h) = h) ∧
      (∀ x : HausdorffCompletionEnvelopeUp,
        hausdorffCompletionEnvelopeFromEventFlow
          (hausdorffCompletionEnvelopeToEventFlow x) = some x) ∧
      (∀ x y : HausdorffCompletionEnvelopeUp,
        hausdorffCompletionEnvelopeToEventFlow x =
          hausdorffCompletionEnvelopeToEventFlow y → x = y) ∧
      hausdorffCompletionEnvelopeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨hausdorffCompletionEnvelopeChapterTasteGate⟩,
      ⟨hausdorffCompletionEnvelopeFieldFaithful⟩,
      ⟨hausdorffCompletionEnvelopeNontrivial⟩,
      hausdorffCompletionEnvelope_decode_encode_bhist,
      hausdorffCompletionEnvelope_round_trip,
      (fun _ _ heq => hausdorffCompletionEnvelopeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffCompletionEnvelopeUp
