import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalInductionStabilitySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalInductionStabilitySealUp : Type where
  | mk : (H F C S L R T P N : BHist) → PhysicalInductionStabilitySealUp
  deriving DecidableEq

def physicalInductionStabilitySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalInductionStabilitySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalInductionStabilitySealEncodeBHist h

def physicalInductionStabilitySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalInductionStabilitySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalInductionStabilitySealDecodeBHist tail)

private theorem physicalInductionStabilitySeal_decode_encode_bhist :
    ∀ h : BHist,
      physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicalInductionStabilitySealToEventFlow :
    PhysicalInductionStabilitySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionStabilitySealUp.mk H F C S L R T P N =>
      [[BMark.b0],
        physicalInductionStabilitySealEncodeBHist H,
        [BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalInductionStabilitySealEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist N]

private def physicalInductionStabilitySealEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      physicalInductionStabilitySealEventAtDefault index rest

def physicalInductionStabilitySealFromEventFlow
    (ef : EventFlow) : Option PhysicalInductionStabilitySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhysicalInductionStabilitySealUp.mk
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 1 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 3 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 5 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 7 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 9 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 11 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 13 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 15 ef))
      (physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEventAtDefault 17 ef)))

private theorem physicalInductionStabilitySeal_round_trip :
    ∀ x : PhysicalInductionStabilitySealUp,
      physicalInductionStabilitySealFromEventFlow
        (physicalInductionStabilitySealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H F C S L R T P N =>
      change
        some
          (PhysicalInductionStabilitySealUp.mk
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist H))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist F))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist C))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist S))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist L))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist R))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist T))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist P))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist N))) =
          some (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)
      rw [physicalInductionStabilitySeal_decode_encode_bhist H,
        physicalInductionStabilitySeal_decode_encode_bhist F,
        physicalInductionStabilitySeal_decode_encode_bhist C,
        physicalInductionStabilitySeal_decode_encode_bhist S,
        physicalInductionStabilitySeal_decode_encode_bhist L,
        physicalInductionStabilitySeal_decode_encode_bhist R,
        physicalInductionStabilitySeal_decode_encode_bhist T,
        physicalInductionStabilitySeal_decode_encode_bhist P,
        physicalInductionStabilitySeal_decode_encode_bhist N]

private theorem physicalInductionStabilitySealToEventFlow_injective
    {x y : PhysicalInductionStabilitySealUp} :
    physicalInductionStabilitySealToEventFlow x =
      physicalInductionStabilitySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalInductionStabilitySealFromEventFlow
          (physicalInductionStabilitySealToEventFlow x) =
        physicalInductionStabilitySealFromEventFlow
          (physicalInductionStabilitySealToEventFlow y) :=
    congrArg physicalInductionStabilitySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalInductionStabilitySeal_round_trip x).symm
      (Eq.trans hread (physicalInductionStabilitySeal_round_trip y)))

private def physicalInductionStabilitySealFields :
    PhysicalInductionStabilitySealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionStabilitySealUp.mk H F C S L R T P N => [H, F, C, S, L, R, T, P, N]

private theorem physicalInductionStabilitySeal_field_faithful :
    ∀ x y : PhysicalInductionStabilitySealUp,
      physicalInductionStabilitySealFields x =
        physicalInductionStabilitySealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H1 F1 C1 S1 L1 R1 T1 P1 N1 =>
      cases y with
      | mk H2 F2 C2 S2 L2 R2 T2 P2 N2 =>
          cases hfields
          rfl

instance physicalInductionStabilitySealBHistCarrier :
    BHistCarrier PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalInductionStabilitySealToEventFlow
  fromEventFlow := physicalInductionStabilitySealFromEventFlow

instance physicalInductionStabilitySealChapterTasteGate :
    ChapterTasteGate PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicalInductionStabilitySealFromEventFlow
        (physicalInductionStabilitySealToEventFlow x) = some x
    exact physicalInductionStabilitySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalInductionStabilitySealToEventFlow_injective heq)

instance physicalInductionStabilitySealFieldFaithful :
    FieldFaithful PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalInductionStabilitySealFields
  field_faithful := physicalInductionStabilitySeal_field_faithful

instance physicalInductionStabilitySealNontrivial :
    Nontrivial PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalInductionStabilitySealUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalInductionStabilitySealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalInductionStabilitySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalInductionStabilitySealChapterTasteGate

theorem PhysicalInductionStabilitySealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEncodeBHist h) = h) ∧
      (∀ x : PhysicalInductionStabilitySealUp,
        physicalInductionStabilitySealFromEventFlow
          (physicalInductionStabilitySealToEventFlow x) = some x) ∧
        (∀ x y : PhysicalInductionStabilitySealUp,
          physicalInductionStabilitySealToEventFlow x =
            physicalInductionStabilitySealToEventFlow y → x = y) ∧
          physicalInductionStabilitySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact physicalInductionStabilitySeal_decode_encode_bhist
  · constructor
    · exact physicalInductionStabilitySeal_round_trip
    · constructor
      · intro x y heq
        exact physicalInductionStabilitySealToEventFlow_injective heq
      · rfl

end BEDC.Derived.PhysicalInductionStabilitySealUp
