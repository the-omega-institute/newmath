import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhenomenologyScienceInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhenomenologyScienceInterfaceUp : Type where
  | mk : (R U O L S J B G H C P N : BHist) → PhenomenologyScienceInterfaceUp

def phenomenologyScienceInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phenomenologyScienceInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phenomenologyScienceInterfaceEncodeBHist h

def phenomenologyScienceInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phenomenologyScienceInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phenomenologyScienceInterfaceDecodeBHist tail)

private theorem phenomenologyScienceInterfaceDecode_encode_bhist :
    ∀ h : BHist,
      phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def phenomenologyScienceInterfaceFields :
    PhenomenologyScienceInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhenomenologyScienceInterfaceUp.mk R U O L S J B G H C P N =>
      [R, U, O, L, S, J, B, G, H, C, P, N]

def phenomenologyScienceInterfaceToEventFlow :
    PhenomenologyScienceInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhenomenologyScienceInterfaceUp.mk R U O L S J B G H C P N =>
      [[BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist R,
        [BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologyScienceInterfaceEncodeBHist N]

private def phenomenologyScienceInterfaceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      phenomenologyScienceInterfaceEventAtDefault index rest

def phenomenologyScienceInterfaceFromEventFlow
    (ef : EventFlow) : Option PhenomenologyScienceInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhenomenologyScienceInterfaceUp.mk
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 1 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 3 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 5 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 7 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 9 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 11 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 13 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 15 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 17 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 19 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 21 ef))
      (phenomenologyScienceInterfaceDecodeBHist
        (phenomenologyScienceInterfaceEventAtDefault 23 ef)))

private theorem phenomenologyScienceInterface_round_trip :
    ∀ x : PhenomenologyScienceInterfaceUp,
      phenomenologyScienceInterfaceFromEventFlow
        (phenomenologyScienceInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R U O L S J B G H C P N =>
      change
        some
          (PhenomenologyScienceInterfaceUp.mk
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist R))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist U))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist O))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist L))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist S))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist J))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist B))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist G))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist H))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist C))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist P))
            (phenomenologyScienceInterfaceDecodeBHist
              (phenomenologyScienceInterfaceEncodeBHist N))) =
          some (PhenomenologyScienceInterfaceUp.mk R U O L S J B G H C P N)
      rw [phenomenologyScienceInterfaceDecode_encode_bhist R,
        phenomenologyScienceInterfaceDecode_encode_bhist U,
        phenomenologyScienceInterfaceDecode_encode_bhist O,
        phenomenologyScienceInterfaceDecode_encode_bhist L,
        phenomenologyScienceInterfaceDecode_encode_bhist S,
        phenomenologyScienceInterfaceDecode_encode_bhist J,
        phenomenologyScienceInterfaceDecode_encode_bhist B,
        phenomenologyScienceInterfaceDecode_encode_bhist G,
        phenomenologyScienceInterfaceDecode_encode_bhist H,
        phenomenologyScienceInterfaceDecode_encode_bhist C,
        phenomenologyScienceInterfaceDecode_encode_bhist P,
        phenomenologyScienceInterfaceDecode_encode_bhist N]

theorem PhenomenologyScienceInterfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhenomenologyScienceInterfaceUp,
      phenomenologyScienceInterfaceFromEventFlow
        (phenomenologyScienceInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact phenomenologyScienceInterface_round_trip

theorem phenomenologyScienceInterfaceToEventFlow_injective
    {x y : PhenomenologyScienceInterfaceUp} :
    phenomenologyScienceInterfaceToEventFlow x =
      phenomenologyScienceInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phenomenologyScienceInterfaceFromEventFlow
          (phenomenologyScienceInterfaceToEventFlow x) =
        phenomenologyScienceInterfaceFromEventFlow
          (phenomenologyScienceInterfaceToEventFlow y) :=
    congrArg phenomenologyScienceInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (phenomenologyScienceInterface_round_trip x).symm
      (Eq.trans hread (phenomenologyScienceInterface_round_trip y)))

private theorem phenomenologyScienceInterface_fields_faithful :
    ∀ x y : PhenomenologyScienceInterfaceUp,
      phenomenologyScienceInterfaceFields x = phenomenologyScienceInterfaceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 U1 O1 L1 S1 J1 B1 G1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 U2 O2 L2 S2 J2 B2 G2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance phenomenologyScienceInterfaceBHistCarrier :
    BHistCarrier PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phenomenologyScienceInterfaceToEventFlow
  fromEventFlow := phenomenologyScienceInterfaceFromEventFlow

instance phenomenologyScienceInterfaceChapterTasteGate :
    ChapterTasteGate PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    exact phenomenologyScienceInterface_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (phenomenologyScienceInterfaceToEventFlow_injective heq)

instance phenomenologyScienceInterfaceFieldFaithful :
    FieldFaithful PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := phenomenologyScienceInterfaceFields
  field_faithful := phenomenologyScienceInterface_fields_faithful

instance phenomenologyScienceInterfaceNontrivial :
    Nontrivial PhenomenologyScienceInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhenomenologyScienceInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhenomenologyScienceInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhenomenologyScienceInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  phenomenologyScienceInterfaceChapterTasteGate

end BEDC.Derived.PhenomenologyScienceInterfaceUp
