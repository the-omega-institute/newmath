import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSubsetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSubsetUp : Type where
  | mk (M S W D R E K H C P N : BHist) : LocatedSubsetUp
  deriving DecidableEq

def locatedSubsetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSubsetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSubsetEncodeBHist h

def locatedSubsetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSubsetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSubsetDecodeBHist tail)

private theorem LocatedSubsetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedSubsetDecodeBHist (locatedSubsetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSubsetFields : LocatedSubsetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSubsetUp.mk M S W D R E K H C P N => [M, S, W, D, R, E, K, H, C, P, N]

def locatedSubsetToEventFlow : LocatedSubsetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedSubsetFields x).map locatedSubsetEncodeBHist

private def locatedSubsetRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => locatedSubsetRawAt n rest

def locatedSubsetFromEventFlow (flow : EventFlow) : Option LocatedSubsetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedSubsetUp.mk
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 0 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 1 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 2 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 3 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 4 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 5 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 6 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 7 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 8 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 9 flow))
      (locatedSubsetDecodeBHist (locatedSubsetRawAt 10 flow)))

private theorem LocatedSubsetTasteGate_single_carrier_alignment_round_trip
    (x : LocatedSubsetUp) :
    locatedSubsetFromEventFlow (locatedSubsetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S W D R E K H C P N =>
      change
        some
          (LocatedSubsetUp.mk
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist M))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist S))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist W))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist D))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist R))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist E))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist K))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist H))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist C))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist P))
            (locatedSubsetDecodeBHist (locatedSubsetEncodeBHist N))) =
          some (LocatedSubsetUp.mk M S W D R E K H C P N)
      rw [LocatedSubsetTasteGate_single_carrier_alignment_decode_encode M,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode S,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode W,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode D,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode R,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode E,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode K,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode H,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode C,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode P,
        LocatedSubsetTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedSubsetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedSubsetUp} :
    locatedSubsetToEventFlow x = locatedSubsetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSubsetFromEventFlow (locatedSubsetToEventFlow x) =
        locatedSubsetFromEventFlow (locatedSubsetToEventFlow y) :=
    congrArg locatedSubsetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedSubsetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedSubsetTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedSubsetTasteGate_single_carrier_alignment_fields :
    ∀ x y : LocatedSubsetUp, locatedSubsetFields x = locatedSubsetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ S₁ W₁ D₁ R₁ E₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ S₂ W₂ D₂ R₂ E₂ K₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedSubsetBHistCarrier : BHistCarrier LocatedSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSubsetToEventFlow
  fromEventFlow := locatedSubsetFromEventFlow

instance locatedSubsetChapterTasteGate : ChapterTasteGate LocatedSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedSubsetFromEventFlow (locatedSubsetToEventFlow x) = some x
    exact LocatedSubsetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedSubsetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedSubsetFieldFaithful : FieldFaithful LocatedSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedSubsetFields
  field_faithful := LocatedSubsetTasteGate_single_carrier_alignment_fields

instance locatedSubsetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedSubsetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedSubsetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedSubsetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedSubsetChapterTasteGate

theorem LocatedSubsetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedSubsetUp) ∧
      Nonempty (FieldFaithful LocatedSubsetUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedSubsetUp) ∧
      (∀ h : BHist, locatedSubsetDecodeBHist (locatedSubsetEncodeBHist h) = h) ∧
      (∀ x : LocatedSubsetUp,
        locatedSubsetFromEventFlow (locatedSubsetToEventFlow x) = some x) ∧
      (∀ x y : LocatedSubsetUp,
        locatedSubsetToEventFlow x = locatedSubsetToEventFlow y → x = y) ∧
      locatedSubsetEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedSubsetChapterTasteGate⟩,
      ⟨locatedSubsetFieldFaithful⟩,
      ⟨locatedSubsetNontrivial⟩,
      LocatedSubsetTasteGate_single_carrier_alignment_decode_encode,
      LocatedSubsetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedSubsetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedSubsetUp
