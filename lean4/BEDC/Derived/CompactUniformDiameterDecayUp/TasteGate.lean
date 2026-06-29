import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformDiameterDecayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformDiameterDecayUp : Type where
  | mk (M K F N L T U H C P : BHist) : CompactUniformDiameterDecayUp
  deriving DecidableEq

def compactUniformDiameterDecayFields : CompactUniformDiameterDecayUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformDiameterDecayUp.mk M K F N L T U H C P =>
      [M, K, F, N, L, T, U, H, C, P]

def compactUniformDiameterDecayEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformDiameterDecayEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformDiameterDecayEncodeBHist h

def compactUniformDiameterDecayDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformDiameterDecayDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformDiameterDecayDecodeBHist tail)

private theorem compactUniformDiameterDecay_decode_encode_bhist :
    ∀ h : BHist,
      compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactUniformDiameterDecayToEventFlow :
    CompactUniformDiameterDecayUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactUniformDiameterDecayFields x).map compactUniformDiameterDecayEncodeBHist

private def compactUniformDiameterDecayEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformDiameterDecayEventAtDefault index rest

def compactUniformDiameterDecayFromEventFlow
    (ef : EventFlow) : Option CompactUniformDiameterDecayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformDiameterDecayUp.mk
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 0 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 1 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 2 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 3 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 4 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 5 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 6 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 7 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 8 ef))
      (compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEventAtDefault 9 ef)))

private theorem compactUniformDiameterDecay_round_trip :
    ∀ x : CompactUniformDiameterDecayUp,
      compactUniformDiameterDecayFromEventFlow
        (compactUniformDiameterDecayToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M K F N L T U H C P =>
      change
        some
          (CompactUniformDiameterDecayUp.mk
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist M))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist K))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist F))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist N))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist L))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist T))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist U))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist H))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist C))
            (compactUniformDiameterDecayDecodeBHist
              (compactUniformDiameterDecayEncodeBHist P))) =
          some (CompactUniformDiameterDecayUp.mk M K F N L T U H C P)
      rw [compactUniformDiameterDecay_decode_encode_bhist M,
        compactUniformDiameterDecay_decode_encode_bhist K,
        compactUniformDiameterDecay_decode_encode_bhist F,
        compactUniformDiameterDecay_decode_encode_bhist N,
        compactUniformDiameterDecay_decode_encode_bhist L,
        compactUniformDiameterDecay_decode_encode_bhist T,
        compactUniformDiameterDecay_decode_encode_bhist U,
        compactUniformDiameterDecay_decode_encode_bhist H,
        compactUniformDiameterDecay_decode_encode_bhist C,
        compactUniformDiameterDecay_decode_encode_bhist P]

private theorem compactUniformDiameterDecayToEventFlow_injective
    {x y : CompactUniformDiameterDecayUp} :
    compactUniformDiameterDecayToEventFlow x =
      compactUniformDiameterDecayToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformDiameterDecayFromEventFlow
          (compactUniformDiameterDecayToEventFlow x) =
        compactUniformDiameterDecayFromEventFlow
          (compactUniformDiameterDecayToEventFlow y) :=
    congrArg compactUniformDiameterDecayFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformDiameterDecay_round_trip x).symm
      (Eq.trans hread (compactUniformDiameterDecay_round_trip y)))

instance compactUniformDiameterDecayBHistCarrier :
    BHistCarrier CompactUniformDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformDiameterDecayToEventFlow
  fromEventFlow := compactUniformDiameterDecayFromEventFlow

instance compactUniformDiameterDecayChapterTasteGate :
    ChapterTasteGate CompactUniformDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformDiameterDecayFromEventFlow
          (compactUniformDiameterDecayToEventFlow x) =
        some x
    exact compactUniformDiameterDecay_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformDiameterDecayToEventFlow_injective heq)

instance compactUniformDiameterDecayFieldFaithful :
    FieldFaithful CompactUniformDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformDiameterDecayFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk M K F N L T U H C P =>
      cases y with
      | mk M' K' F' N' L' T' U' H' C' P' =>
          cases hfields
          rfl

def taste_gate : ChapterTasteGate CompactUniformDiameterDecayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformDiameterDecayChapterTasteGate

theorem CompactUniformDiameterDecayTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactUniformDiameterDecayDecodeBHist
        (compactUniformDiameterDecayEncodeBHist h) = h) /\
      (forall x : CompactUniformDiameterDecayUp,
        compactUniformDiameterDecayFromEventFlow
          (compactUniformDiameterDecayToEventFlow x) = some x) /\
      (forall x y : CompactUniformDiameterDecayUp,
        compactUniformDiameterDecayToEventFlow x =
          compactUniformDiameterDecayToEventFlow y -> x = y) /\
      compactUniformDiameterDecayEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactUniformDiameterDecay_decode_encode_bhist
  · constructor
    · exact compactUniformDiameterDecay_round_trip
    · constructor
      · intro x y heq
        exact compactUniformDiameterDecayToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompactUniformDiameterDecayUp
