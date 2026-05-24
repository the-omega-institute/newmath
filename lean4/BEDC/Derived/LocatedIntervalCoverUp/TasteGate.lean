import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalCoverUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalCoverUp : Type where
  | mk (I Q D R W S H K P N : BHist) : LocatedIntervalCoverUp
  deriving DecidableEq

def locatedIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalCoverEncodeBHist h

def locatedIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalCoverDecodeBHist tail)

private theorem locatedIntervalCover_decode_encode_bhist :
    ∀ h : BHist, locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalCoverFields : LocatedIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalCoverUp.mk I Q D R W S H K P N => [I, Q, D, R, W, S, H, K, P, N]

def locatedIntervalCoverToEventFlow : LocatedIntervalCoverUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalCoverFields x).map locatedIntervalCoverEncodeBHist

private def locatedIntervalCoverRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locatedIntervalCoverRawAt n rest

def locatedIntervalCoverFromEventFlow (flow : EventFlow) : Option LocatedIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalCoverUp.mk
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 0 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 1 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 2 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 3 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 4 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 5 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 6 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 7 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 8 flow))
      (locatedIntervalCoverDecodeBHist (locatedIntervalCoverRawAt 9 flow)))

private theorem locatedIntervalCover_round_trip :
    ∀ x : LocatedIntervalCoverUp,
      locatedIntervalCoverFromEventFlow (locatedIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Q D R W S H K P N =>
      change
        some
          (LocatedIntervalCoverUp.mk
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist I))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist Q))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist D))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist R))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist W))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist S))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist H))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist K))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist P))
            (locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist N))) =
          some (LocatedIntervalCoverUp.mk I Q D R W S H K P N)
      rw [locatedIntervalCover_decode_encode_bhist I,
        locatedIntervalCover_decode_encode_bhist Q,
        locatedIntervalCover_decode_encode_bhist D,
        locatedIntervalCover_decode_encode_bhist R,
        locatedIntervalCover_decode_encode_bhist W,
        locatedIntervalCover_decode_encode_bhist S,
        locatedIntervalCover_decode_encode_bhist H,
        locatedIntervalCover_decode_encode_bhist K,
        locatedIntervalCover_decode_encode_bhist P,
        locatedIntervalCover_decode_encode_bhist N]

private theorem locatedIntervalCoverToEventFlow_injective {x y : LocatedIntervalCoverUp} :
    locatedIntervalCoverToEventFlow x = locatedIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalCoverFromEventFlow (locatedIntervalCoverToEventFlow x) =
        locatedIntervalCoverFromEventFlow (locatedIntervalCoverToEventFlow y) :=
    congrArg locatedIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalCover_round_trip x).symm
      (Eq.trans hread (locatedIntervalCover_round_trip y)))

private theorem locatedIntervalCover_fields_faithful :
    ∀ x y : LocatedIntervalCoverUp, locatedIntervalCoverFields x = locatedIntervalCoverFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ Q₁ D₁ R₁ W₁ S₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk I₂ Q₂ D₂ R₂ W₂ S₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedIntervalCoverBHistCarrier : BHistCarrier LocatedIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalCoverToEventFlow
  fromEventFlow := locatedIntervalCoverFromEventFlow

instance locatedIntervalCoverChapterTasteGate :
    ChapterTasteGate LocatedIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntervalCoverFromEventFlow (locatedIntervalCoverToEventFlow x) = some x
    exact locatedIntervalCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalCoverToEventFlow_injective heq)

instance locatedIntervalCoverFieldFaithful : FieldFaithful LocatedIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedIntervalCoverFields
  field_faithful := locatedIntervalCover_fields_faithful

instance locatedIntervalCoverNontrivial : Nontrivial LocatedIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedIntervalCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedIntervalCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalCoverChapterTasteGate

theorem LocatedIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedIntervalCoverDecodeBHist (locatedIntervalCoverEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalCoverUp,
        locatedIntervalCoverFromEventFlow (locatedIntervalCoverToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalCoverUp,
          locatedIntervalCoverToEventFlow x = locatedIntervalCoverToEventFlow y → x = y) ∧
          locatedIntervalCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨locatedIntervalCover_decode_encode_bhist,
      locatedIntervalCover_round_trip,
      fun _ _ heq => locatedIntervalCoverToEventFlow_injective heq,
      rfl⟩

end TasteGate
end BEDC.Derived.LocatedIntervalCoverUp
