import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformSpaceUp : Type where
  | mk (U D A W T F N H C P Q : BHist) : LocatedUniformSpaceUp
  deriving DecidableEq

def locatedUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformSpaceEncodeBHist h

def locatedUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformSpaceDecodeBHist tail)

private theorem LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformSpaceFields : LocatedUniformSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformSpaceUp.mk U D A W T F N H C P Q => [U, D, A, W, T, F, N, H, C, P, Q]

def locatedUniformSpaceToEventFlow : LocatedUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedUniformSpaceFields x).map locatedUniformSpaceEncodeBHist

private def locatedUniformSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedUniformSpaceEventAt index rest

def locatedUniformSpaceFromEventFlow (ef : EventFlow) : Option LocatedUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedUniformSpaceUp.mk
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 0 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 1 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 2 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 3 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 4 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 5 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 6 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 7 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 8 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 9 ef))
      (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEventAt 10 ef)))

private theorem LocatedUniformSpaceTasteGate_single_carrier_alignment_round_trip
    (x : LocatedUniformSpaceUp) :
    locatedUniformSpaceFromEventFlow (locatedUniformSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U D A W T F N H C P Q =>
      change
        some
          (LocatedUniformSpaceUp.mk
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist U))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist D))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist A))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist W))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist T))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist F))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist N))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist H))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist C))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist P))
            (locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist Q))) =
          some (LocatedUniformSpaceUp.mk U D A W T F N H C P Q)
      rw [LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode U,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode D,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode A,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode W,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode T,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode F,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode N,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode H,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode C,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode P,
        LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode Q]

private theorem LocatedUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedUniformSpaceUp} :
    locatedUniformSpaceToEventFlow x = locatedUniformSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformSpaceFromEventFlow (locatedUniformSpaceToEventFlow x) =
        locatedUniformSpaceFromEventFlow (locatedUniformSpaceToEventFlow y) :=
    congrArg locatedUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedUniformSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedUniformSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedUniformSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedUniformSpaceUp, locatedUniformSpaceFields x = locatedUniformSpaceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ D₁ A₁ W₁ T₁ F₁ N₁ H₁ C₁ P₁ Q₁ =>
      cases y with
      | mk U₂ D₂ A₂ W₂ T₂ F₂ N₂ H₂ C₂ P₂ Q₂ =>
          cases hfields
          rfl

instance locatedUniformSpaceBHistCarrier : BHistCarrier LocatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformSpaceToEventFlow
  fromEventFlow := locatedUniformSpaceFromEventFlow

instance locatedUniformSpaceChapterTasteGate : ChapterTasteGate LocatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedUniformSpaceFromEventFlow (locatedUniformSpaceToEventFlow x) = some x
    exact LocatedUniformSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedUniformSpaceFieldFaithful : FieldFaithful LocatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedUniformSpaceFields
  field_faithful := LocatedUniformSpaceTasteGate_single_carrier_alignment_fields_faithful

instance locatedUniformSpaceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedUniformSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedUniformSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedUniformSpaceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedUniformSpaceChapterTasteGate

theorem LocatedUniformSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedUniformSpaceDecodeBHist (locatedUniformSpaceEncodeBHist h) = h) ∧
      (∀ x : LocatedUniformSpaceUp,
        locatedUniformSpaceFromEventFlow (locatedUniformSpaceToEventFlow x) = some x) ∧
        (∀ x y : LocatedUniformSpaceUp,
          locatedUniformSpaceToEventFlow x = locatedUniformSpaceToEventFlow y → x = y) ∧
          locatedUniformSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨LocatedUniformSpaceTasteGate_single_carrier_alignment_decode_encode,
      LocatedUniformSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LocatedUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedUniformSpaceUp.TasteGate

namespace BEDC.Derived.LocatedUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem LocatedUniformSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.locatedUniformSpaceDecodeBHist (TasteGate.locatedUniformSpaceEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.LocatedUniformSpaceUp,
        TasteGate.locatedUniformSpaceFromEventFlow
            (TasteGate.locatedUniformSpaceToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.LocatedUniformSpaceUp,
          TasteGate.locatedUniformSpaceToEventFlow x =
              TasteGate.locatedUniformSpaceToEventFlow y →
            x = y) ∧
          TasteGate.locatedUniformSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact TasteGate.LocatedUniformSpaceTasteGate_single_carrier_alignment

end BEDC.Derived.LocatedUniformSpaceUp
