import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OpenIntervalRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OpenIntervalRealUp : Type where
  | mk (A B X L U D S R H C P N : BHist) : OpenIntervalRealUp
  deriving DecidableEq

def openIntervalRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: openIntervalRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: openIntervalRealEncodeBHist h

def openIntervalRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (openIntervalRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (openIntervalRealDecodeBHist tail)

private theorem OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, openIntervalRealDecodeBHist (openIntervalRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def openIntervalRealFields : OpenIntervalRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OpenIntervalRealUp.mk A B X L U D S R H C P N => [A, B, X, L, U, D, S, R, H, C, P, N]

def openIntervalRealToEventFlow : OpenIntervalRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (openIntervalRealFields x).map openIntervalRealEncodeBHist

private def openIntervalRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => openIntervalRealEventAtDefault index rest

def openIntervalRealFromEventFlow (ef : EventFlow) : Option OpenIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (OpenIntervalRealUp.mk
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 0 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 1 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 2 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 3 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 4 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 5 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 6 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 7 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 8 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 9 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 10 ef))
      (openIntervalRealDecodeBHist (openIntervalRealEventAtDefault 11 ef)))

private theorem OpenIntervalRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OpenIntervalRealUp, openIntervalRealFromEventFlow (openIntervalRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B X L U D S R H C P N =>
      change
        some (OpenIntervalRealUp.mk
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist A))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist B))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist X))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist L))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist U))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist D))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist S))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist R))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist H))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist C))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist P))
          (openIntervalRealDecodeBHist (openIntervalRealEncodeBHist N))
          ) = some (OpenIntervalRealUp.mk A B X L U D S R H C P N)
      rw [OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode A, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode B, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode X, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode L, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode U, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode D, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode S, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode R, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode H, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode C, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode P, OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem OpenIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OpenIntervalRealUp} :
    openIntervalRealToEventFlow x = openIntervalRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      openIntervalRealFromEventFlow (openIntervalRealToEventFlow x) =
        openIntervalRealFromEventFlow (openIntervalRealToEventFlow y) :=
    congrArg openIntervalRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OpenIntervalRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OpenIntervalRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem OpenIntervalRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : OpenIntervalRealUp, openIntervalRealFields x = openIntervalRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ X₁ L₁ U₁ D₁ S₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ X₂ L₂ U₂ D₂ S₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance openIntervalRealBHistCarrier : BHistCarrier OpenIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := openIntervalRealToEventFlow
  fromEventFlow := openIntervalRealFromEventFlow

instance openIntervalRealChapterTasteGate : ChapterTasteGate OpenIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change openIntervalRealFromEventFlow (openIntervalRealToEventFlow x) = some x
    exact OpenIntervalRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OpenIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance openIntervalRealFieldFaithful : FieldFaithful OpenIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := openIntervalRealFields
  field_faithful := OpenIntervalRealTasteGate_single_carrier_alignment_fields_faithful

instance openIntervalRealNontrivial : Nontrivial OpenIntervalRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OpenIntervalRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OpenIntervalRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OpenIntervalRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  openIntervalRealChapterTasteGate

theorem OpenIntervalRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, openIntervalRealDecodeBHist (openIntervalRealEncodeBHist h) = h) ∧
      (∀ x : OpenIntervalRealUp, openIntervalRealFromEventFlow (openIntervalRealToEventFlow x) = some x) ∧
        (∀ x y : OpenIntervalRealUp,
          openIntervalRealToEventFlow x = openIntervalRealToEventFlow y → x = y) ∧
          openIntervalRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨OpenIntervalRealTasteGate_single_carrier_alignment_decode_encode,
      OpenIntervalRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => OpenIntervalRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.OpenIntervalRealUp
