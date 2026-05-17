import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhenomenologicalFrameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhenomenologicalFrameUp : Type where
  | mk : (L M U O G A T H C P R N : BHist) → PhenomenologicalFrameUp

def phenomenologicalFrameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: phenomenologicalFrameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: phenomenologicalFrameEncodeBHist h

def phenomenologicalFrameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (phenomenologicalFrameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (phenomenologicalFrameDecodeBHist tail)

private theorem phenomenologicalFrameDecode_encode_bhist :
    ∀ h : BHist,
      phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def phenomenologicalFrameFields : PhenomenologicalFrameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhenomenologicalFrameUp.mk L M U O G A T H C P R N =>
      [L, M, U, O, G, A, T, H, C, P, R, N]

def phenomenologicalFrameToEventFlow : PhenomenologicalFrameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhenomenologicalFrameUp.mk L M U O G A T H C P R N =>
      [[BMark.b0],
        phenomenologicalFrameEncodeBHist L,
        [BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        phenomenologicalFrameEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        phenomenologicalFrameEncodeBHist N]

private def phenomenologicalFrameEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      phenomenologicalFrameEventAtDefault index rest

def phenomenologicalFrameFromEventFlow
    (ef : EventFlow) : Option PhenomenologicalFrameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PhenomenologicalFrameUp.mk
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 1 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 3 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 5 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 7 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 9 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 11 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 13 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 15 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 17 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 19 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 21 ef))
      (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEventAtDefault 23 ef)))

private theorem phenomenologicalFrame_round_trip :
    ∀ x : PhenomenologicalFrameUp,
      phenomenologicalFrameFromEventFlow (phenomenologicalFrameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L M U O G A T H C P R N =>
      change
        some
          (PhenomenologicalFrameUp.mk
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist L))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist M))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist U))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist O))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist G))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist A))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist T))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist H))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist C))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist P))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist R))
            (phenomenologicalFrameDecodeBHist (phenomenologicalFrameEncodeBHist N))) =
          some (PhenomenologicalFrameUp.mk L M U O G A T H C P R N)
      rw [phenomenologicalFrameDecode_encode_bhist L,
        phenomenologicalFrameDecode_encode_bhist M,
        phenomenologicalFrameDecode_encode_bhist U,
        phenomenologicalFrameDecode_encode_bhist O,
        phenomenologicalFrameDecode_encode_bhist G,
        phenomenologicalFrameDecode_encode_bhist A,
        phenomenologicalFrameDecode_encode_bhist T,
        phenomenologicalFrameDecode_encode_bhist H,
        phenomenologicalFrameDecode_encode_bhist C,
        phenomenologicalFrameDecode_encode_bhist P,
        phenomenologicalFrameDecode_encode_bhist R,
        phenomenologicalFrameDecode_encode_bhist N]

theorem PhenomenologicalFrameTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhenomenologicalFrameUp,
      phenomenologicalFrameFromEventFlow (phenomenologicalFrameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact phenomenologicalFrame_round_trip

theorem phenomenologicalFrameToEventFlow_injective {x y : PhenomenologicalFrameUp} :
    phenomenologicalFrameToEventFlow x = phenomenologicalFrameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      phenomenologicalFrameFromEventFlow (phenomenologicalFrameToEventFlow x) =
        phenomenologicalFrameFromEventFlow (phenomenologicalFrameToEventFlow y) :=
    congrArg phenomenologicalFrameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (phenomenologicalFrame_round_trip x).symm
      (Eq.trans hread (phenomenologicalFrame_round_trip y)))

private theorem phenomenologicalFrame_fields_faithful :
    ∀ x y : PhenomenologicalFrameUp,
      phenomenologicalFrameFields x = phenomenologicalFrameFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 M1 U1 O1 G1 A1 T1 H1 C1 P1 R1 N1 =>
      cases y with
      | mk L2 M2 U2 O2 G2 A2 T2 H2 C2 P2 R2 N2 =>
          cases hfields
          rfl

instance phenomenologicalFrameBHistCarrier : BHistCarrier PhenomenologicalFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := phenomenologicalFrameToEventFlow
  fromEventFlow := phenomenologicalFrameFromEventFlow

instance phenomenologicalFrameChapterTasteGate :
    ChapterTasteGate PhenomenologicalFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    exact phenomenologicalFrame_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (phenomenologicalFrameToEventFlow_injective heq)

instance phenomenologicalFrameFieldFaithful :
    FieldFaithful PhenomenologicalFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := phenomenologicalFrameFields
  field_faithful := phenomenologicalFrame_fields_faithful

instance phenomenologicalFrameNontrivial : Nontrivial PhenomenologicalFrameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhenomenologicalFrameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhenomenologicalFrameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhenomenologicalFrameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  phenomenologicalFrameChapterTasteGate

end BEDC.Derived.PhenomenologicalFrameUp
