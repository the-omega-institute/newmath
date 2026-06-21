import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocaleSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocaleSpaceUp : Type where
  | mk : (openIndex finiteJoin finiteMeet endpoints cover boundary membership transport
      replay provenance name : BHist) → LocaleSpaceUp
  deriving DecidableEq

def localeSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localeSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localeSpaceEncodeBHist h

def localeSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localeSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localeSpaceDecodeBHist tail)

private theorem localeSpace_decode_encode_bhist :
    ∀ h : BHist, localeSpaceDecodeBHist (localeSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def localeSpaceFields : LocaleSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocaleSpaceUp.mk openIndex finiteJoin finiteMeet endpoints cover boundary membership
      transport replay provenance name =>
      [openIndex, finiteJoin, finiteMeet, endpoints, cover, boundary, membership, transport,
        replay, provenance, name]

def localeSpaceToEventFlow : LocaleSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (localeSpaceFields x).map localeSpaceEncodeBHist

private def localeSpaceDecodePacket
    (openIndex finiteJoin finiteMeet endpoints cover boundary membership transport replay
      provenance name : RawEvent) : LocaleSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocaleSpaceUp.mk
    (localeSpaceDecodeBHist openIndex)
    (localeSpaceDecodeBHist finiteJoin)
    (localeSpaceDecodeBHist finiteMeet)
    (localeSpaceDecodeBHist endpoints)
    (localeSpaceDecodeBHist cover)
    (localeSpaceDecodeBHist boundary)
    (localeSpaceDecodeBHist membership)
    (localeSpaceDecodeBHist transport)
    (localeSpaceDecodeBHist replay)
    (localeSpaceDecodeBHist provenance)
    (localeSpaceDecodeBHist name)

private def localeSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => localeSpaceRawAt n rest

private def localeSpaceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => localeSpaceLengthEq n rest

def localeSpaceFromEventFlow : EventFlow → Option LocaleSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match localeSpaceLengthEq 11 flow with
      | true =>
          some
            (localeSpaceDecodePacket
              (localeSpaceRawAt 0 flow)
              (localeSpaceRawAt 1 flow)
              (localeSpaceRawAt 2 flow)
              (localeSpaceRawAt 3 flow)
              (localeSpaceRawAt 4 flow)
              (localeSpaceRawAt 5 flow)
              (localeSpaceRawAt 6 flow)
              (localeSpaceRawAt 7 flow)
              (localeSpaceRawAt 8 flow)
              (localeSpaceRawAt 9 flow)
              (localeSpaceRawAt 10 flow))
      | false => none

private theorem localeSpace_round_trip :
    ∀ x : LocaleSpaceUp, localeSpaceFromEventFlow (localeSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk openIndex finiteJoin finiteMeet endpoints cover boundary membership transport replay
      provenance name =>
      change
        some
          (localeSpaceDecodePacket
            (localeSpaceEncodeBHist openIndex)
            (localeSpaceEncodeBHist finiteJoin)
            (localeSpaceEncodeBHist finiteMeet)
            (localeSpaceEncodeBHist endpoints)
            (localeSpaceEncodeBHist cover)
            (localeSpaceEncodeBHist boundary)
            (localeSpaceEncodeBHist membership)
            (localeSpaceEncodeBHist transport)
            (localeSpaceEncodeBHist replay)
            (localeSpaceEncodeBHist provenance)
            (localeSpaceEncodeBHist name)) =
          some
            (LocaleSpaceUp.mk openIndex finiteJoin finiteMeet endpoints cover boundary
              membership transport replay provenance name)
      unfold localeSpaceDecodePacket
      rw [localeSpace_decode_encode_bhist openIndex,
        localeSpace_decode_encode_bhist finiteJoin,
        localeSpace_decode_encode_bhist finiteMeet,
        localeSpace_decode_encode_bhist endpoints,
        localeSpace_decode_encode_bhist cover,
        localeSpace_decode_encode_bhist boundary,
        localeSpace_decode_encode_bhist membership,
        localeSpace_decode_encode_bhist transport,
        localeSpace_decode_encode_bhist replay,
        localeSpace_decode_encode_bhist provenance,
        localeSpace_decode_encode_bhist name]

private theorem localeSpaceToEventFlow_injective {x y : LocaleSpaceUp} :
    localeSpaceToEventFlow x = localeSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localeSpaceFromEventFlow (localeSpaceToEventFlow x) =
        localeSpaceFromEventFlow (localeSpaceToEventFlow y) :=
    congrArg localeSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localeSpace_round_trip x).symm
      (Eq.trans hread (localeSpace_round_trip y)))

private theorem localeSpace_fields_faithful :
    ∀ x y : LocaleSpaceUp, localeSpaceFields x = localeSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk openIndex₁ finiteJoin₁ finiteMeet₁ endpoints₁ cover₁ boundary₁ membership₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk openIndex₂ finiteJoin₂ finiteMeet₂ endpoints₂ cover₂ boundary₂ membership₂
          transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance localeSpaceBHistCarrier : BHistCarrier LocaleSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localeSpaceToEventFlow
  fromEventFlow := localeSpaceFromEventFlow

instance localeSpaceChapterTasteGate : ChapterTasteGate LocaleSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change localeSpaceFromEventFlow (localeSpaceToEventFlow x) = some x
    exact localeSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localeSpaceToEventFlow_injective heq)

instance localeSpaceFieldFaithful : FieldFaithful LocaleSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := localeSpaceFields
  field_faithful := localeSpace_fields_faithful

instance localeSpaceNontrivial : Nontrivial LocaleSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocaleSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocaleSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocaleSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localeSpaceChapterTasteGate

theorem LocaleSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocaleSpaceUp) ∧
      Nonempty (FieldFaithful LocaleSpaceUp) ∧
        Nonempty (Nontrivial LocaleSpaceUp) ∧
          (∀ h : BHist, localeSpaceDecodeBHist (localeSpaceEncodeBHist h) = h) ∧
            (∀ x : LocaleSpaceUp,
              localeSpaceFromEventFlow (localeSpaceToEventFlow x) = some x) ∧
              localeSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨localeSpaceChapterTasteGate⟩,
      ⟨localeSpaceFieldFaithful⟩,
      ⟨localeSpaceNontrivial⟩,
      localeSpace_decode_encode_bhist,
      localeSpace_round_trip,
      rfl⟩

end BEDC.Derived.LocaleSpaceUp
