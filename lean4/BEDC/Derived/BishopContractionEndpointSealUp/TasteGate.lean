import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopContractionEndpointSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopContractionEndpointSealUp : Type where
  | mk (I F Q R X H C P N : BHist) : BishopContractionEndpointSealUp
  deriving DecidableEq

def bishopContractionEndpointSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopContractionEndpointSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopContractionEndpointSealEncodeBHist h

def bishopContractionEndpointSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopContractionEndpointSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopContractionEndpointSealDecodeBHist tail)

theorem BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      bishopContractionEndpointSealDecodeBHist
        (bishopContractionEndpointSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopContractionEndpointSealFields :
    BishopContractionEndpointSealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopContractionEndpointSealUp.mk I F Q R X H C P N => [I, F, Q, R, X, H, C, P, N]

def bishopContractionEndpointSealToEventFlow :
    BishopContractionEndpointSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopContractionEndpointSealFields x).map bishopContractionEndpointSealEncodeBHist

private def bishopContractionEndpointSealEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopContractionEndpointSealEventAt index rest

def bishopContractionEndpointSealFromEventFlow :
    EventFlow -> Option BishopContractionEndpointSealUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopContractionEndpointSealUp.mk
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 0 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 1 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 2 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 3 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 4 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 5 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 6 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 7 ef))
      (bishopContractionEndpointSealDecodeBHist (bishopContractionEndpointSealEventAt 8 ef)))

theorem BishopContractionEndpointSealTasteGate_single_carrier_alignment_round_trip
    (x : BishopContractionEndpointSealUp) :
    bishopContractionEndpointSealFromEventFlow
      (bishopContractionEndpointSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F Q R X H C P N =>
      change
        some
          (BishopContractionEndpointSealUp.mk
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist I))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist F))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist Q))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist R))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist X))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist H))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist C))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist P))
            (bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist N))) =
          some (BishopContractionEndpointSealUp.mk I F Q R X H C P N)
      rw [BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode I,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode F,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode Q,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode R,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode X,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode H,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode C,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode P,
        BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode N]

theorem BishopContractionEndpointSealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopContractionEndpointSealUp} :
    bishopContractionEndpointSealToEventFlow x =
      bishopContractionEndpointSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopContractionEndpointSealFromEventFlow
          (bishopContractionEndpointSealToEventFlow x) =
        bishopContractionEndpointSealFromEventFlow
          (bishopContractionEndpointSealToEventFlow y) :=
    congrArg bishopContractionEndpointSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopContractionEndpointSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopContractionEndpointSealTasteGate_single_carrier_alignment_round_trip y)))

theorem BishopContractionEndpointSealTasteGate_single_carrier_alignment_field_faithful :
    forall x y : BishopContractionEndpointSealUp,
      bishopContractionEndpointSealFields x = bishopContractionEndpointSealFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 F1 Q1 R1 X1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 F2 Q2 R2 X2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopContractionEndpointSealBHistCarrier :
    BHistCarrier BishopContractionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopContractionEndpointSealToEventFlow
  fromEventFlow := bishopContractionEndpointSealFromEventFlow

instance bishopContractionEndpointSealChapterTasteGate :
    ChapterTasteGate BishopContractionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := BishopContractionEndpointSealTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopContractionEndpointSealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopContractionEndpointSealFieldFaithful :
    FieldFaithful BishopContractionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopContractionEndpointSealFields
  field_faithful :=
    BishopContractionEndpointSealTasteGate_single_carrier_alignment_field_faithful

instance bishopContractionEndpointSealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopContractionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopContractionEndpointSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopContractionEndpointSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopContractionEndpointSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopContractionEndpointSealUp) /\
      Nonempty (FieldFaithful BishopContractionEndpointSealUp) /\
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopContractionEndpointSealUp) /\
          (forall h : BHist,
            bishopContractionEndpointSealDecodeBHist
              (bishopContractionEndpointSealEncodeBHist h) = h) /\
            bishopContractionEndpointSealEncodeBHist BHist.Empty = ([] : List BMark) /\
              (forall x : BishopContractionEndpointSealUp,
                bishopContractionEndpointSealFromEventFlow
                  (bishopContractionEndpointSealToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨bishopContractionEndpointSealChapterTasteGate⟩
  · constructor
    · exact ⟨bishopContractionEndpointSealFieldFaithful⟩
    · constructor
      · exact ⟨bishopContractionEndpointSealNontrivial⟩
      · constructor
        · exact BishopContractionEndpointSealTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · rfl
          · exact BishopContractionEndpointSealTasteGate_single_carrier_alignment_round_trip

end BEDC.Derived.BishopContractionEndpointSealUp
