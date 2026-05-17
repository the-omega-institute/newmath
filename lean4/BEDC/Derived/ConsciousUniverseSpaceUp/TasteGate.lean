import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConsciousUniverseSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConsciousUniverseSpaceUp : Type where
  | mk (L U T S I H C P N : BHist) : ConsciousUniverseSpaceUp
  deriving DecidableEq

def consciousUniverseSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: consciousUniverseSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: consciousUniverseSpaceEncodeBHist h

def consciousUniverseSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (consciousUniverseSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (consciousUniverseSpaceDecodeBHist tail)

private theorem consciousUniverseSpaceDecode_encode_bhist :
    ∀ h : BHist,
      consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def consciousUniverseSpaceFields : ConsciousUniverseSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConsciousUniverseSpaceUp.mk L U T S I H C P N => [L, U, T, S, I, H, C, P, N]

def consciousUniverseSpaceToEventFlow : ConsciousUniverseSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConsciousUniverseSpaceUp.mk L U T S I H C P N =>
      [[BMark.b0],
        consciousUniverseSpaceEncodeBHist L,
        [BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        consciousUniverseSpaceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        consciousUniverseSpaceEncodeBHist N]

private def consciousUniverseSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => consciousUniverseSpaceRawAt n rest

def consciousUniverseSpaceFromEventFlow : EventFlow → Option ConsciousUniverseSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (ConsciousUniverseSpaceUp.mk
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 1 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 3 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 5 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 7 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 9 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 11 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 13 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 15 flow))
          (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceRawAt 17 flow)))

private theorem consciousUniverseSpace_round_trip :
    ∀ x : ConsciousUniverseSpaceUp,
      consciousUniverseSpaceFromEventFlow
        (consciousUniverseSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U T S I H C P N =>
      change
        some
          (ConsciousUniverseSpaceUp.mk
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist L))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist U))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist T))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist S))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist I))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist H))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist C))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist P))
            (consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist N))) =
          some (ConsciousUniverseSpaceUp.mk L U T S I H C P N)
      rw [consciousUniverseSpaceDecode_encode_bhist L,
        consciousUniverseSpaceDecode_encode_bhist U,
        consciousUniverseSpaceDecode_encode_bhist T,
        consciousUniverseSpaceDecode_encode_bhist S,
        consciousUniverseSpaceDecode_encode_bhist I,
        consciousUniverseSpaceDecode_encode_bhist H,
        consciousUniverseSpaceDecode_encode_bhist C,
        consciousUniverseSpaceDecode_encode_bhist P,
        consciousUniverseSpaceDecode_encode_bhist N]

private theorem consciousUniverseSpaceToEventFlow_injective
    {x y : ConsciousUniverseSpaceUp} :
    consciousUniverseSpaceToEventFlow x = consciousUniverseSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      consciousUniverseSpaceFromEventFlow (consciousUniverseSpaceToEventFlow x) =
        consciousUniverseSpaceFromEventFlow (consciousUniverseSpaceToEventFlow y) :=
    congrArg consciousUniverseSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (consciousUniverseSpace_round_trip x).symm
      (Eq.trans hread (consciousUniverseSpace_round_trip y)))

private theorem consciousUniverseSpace_field_faithful :
    ∀ x y : ConsciousUniverseSpaceUp,
      consciousUniverseSpaceFields x = consciousUniverseSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 T1 S1 I1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 T2 S2 I2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance consciousUniverseSpaceBHistCarrier : BHistCarrier ConsciousUniverseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := consciousUniverseSpaceToEventFlow
  fromEventFlow := consciousUniverseSpaceFromEventFlow

instance consciousUniverseSpaceChapterTasteGate :
    ChapterTasteGate ConsciousUniverseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      consciousUniverseSpaceFromEventFlow
        (consciousUniverseSpaceToEventFlow x) = some x
    exact consciousUniverseSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (consciousUniverseSpaceToEventFlow_injective heq)

instance consciousUniverseSpaceFieldFaithful : FieldFaithful ConsciousUniverseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := consciousUniverseSpaceFields
  field_faithful := consciousUniverseSpace_field_faithful

instance consciousUniverseSpaceNontrivial : Nontrivial ConsciousUniverseSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConsciousUniverseSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConsciousUniverseSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConsciousUniverseSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  consciousUniverseSpaceChapterTasteGate

theorem ConsciousUniverseSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, consciousUniverseSpaceDecodeBHist (consciousUniverseSpaceEncodeBHist h) = h) ∧
      Nonempty (Nontrivial ConsciousUniverseSpaceUp) ∧
        Nonempty (ChapterTasteGate ConsciousUniverseSpaceUp) ∧
          Nonempty (FieldFaithful ConsciousUniverseSpaceUp) ∧
            consciousUniverseSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨consciousUniverseSpaceDecode_encode_bhist,
      ⟨consciousUniverseSpaceNontrivial⟩,
      ⟨consciousUniverseSpaceChapterTasteGate⟩,
      ⟨consciousUniverseSpaceFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.ConsciousUniverseSpaceUp
