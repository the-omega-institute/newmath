import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedTypeCheckerSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedTypeCheckerSealUp : Type where
  | mk (C T Q E N R O H K P L : BHist) : ClosedTypeCheckerSealUp
  deriving DecidableEq

def closedTypeCheckerSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedTypeCheckerSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedTypeCheckerSealEncodeBHist h

def closedTypeCheckerSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedTypeCheckerSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedTypeCheckerSealDecodeBHist tail)

private theorem ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedTypeCheckerSealFields : ClosedTypeCheckerSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedTypeCheckerSealUp.mk C T Q E N R O H K P L => [C, T, Q, E, N, R, O, H, K, P, L]

def closedTypeCheckerSealToEventFlow : ClosedTypeCheckerSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedTypeCheckerSealFields x).map closedTypeCheckerSealEncodeBHist

private def closedTypeCheckerSealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedTypeCheckerSealEventAt index rest

def closedTypeCheckerSealFromEventFlow (ef : EventFlow) : Option ClosedTypeCheckerSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedTypeCheckerSealUp.mk
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 0 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 1 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 2 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 3 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 4 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 5 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 6 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 7 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 8 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 9 ef))
      (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEventAt 10 ef)))

private theorem ClosedTypeCheckerSealTasteGate_single_carrier_alignment_round_trip
    (x : ClosedTypeCheckerSealUp) :
    closedTypeCheckerSealFromEventFlow (closedTypeCheckerSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C T Q E N R O H K P L =>
      change
        some
          (ClosedTypeCheckerSealUp.mk
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist C))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist T))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist Q))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist E))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist N))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist R))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist O))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist H))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist K))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist P))
            (closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist L))) =
          some (ClosedTypeCheckerSealUp.mk C T Q E N R O H K P L)
      rw [ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode C,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode T,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode Q,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode E,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode N,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode R,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode O,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode H,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode K,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode P,
        ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode L]

private theorem ClosedTypeCheckerSealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ClosedTypeCheckerSealUp} :
    closedTypeCheckerSealToEventFlow x = closedTypeCheckerSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedTypeCheckerSealFromEventFlow (closedTypeCheckerSealToEventFlow x) =
        closedTypeCheckerSealFromEventFlow (closedTypeCheckerSealToEventFlow y) :=
    congrArg closedTypeCheckerSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedTypeCheckerSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedTypeCheckerSealTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedTypeCheckerSealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ClosedTypeCheckerSealUp, closedTypeCheckerSealFields x = closedTypeCheckerSealFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ T₁ Q₁ E₁ N₁ R₁ O₁ H₁ K₁ P₁ L₁ =>
      cases y with
      | mk C₂ T₂ Q₂ E₂ N₂ R₂ O₂ H₂ K₂ P₂ L₂ =>
          cases hfields
          rfl

instance closedTypeCheckerSealBHistCarrier : BHistCarrier ClosedTypeCheckerSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedTypeCheckerSealToEventFlow
  fromEventFlow := closedTypeCheckerSealFromEventFlow

instance closedTypeCheckerSealChapterTasteGate : ChapterTasteGate ClosedTypeCheckerSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedTypeCheckerSealFromEventFlow (closedTypeCheckerSealToEventFlow x) = some x
    exact ClosedTypeCheckerSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedTypeCheckerSealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance closedTypeCheckerSealFieldFaithful : FieldFaithful ClosedTypeCheckerSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedTypeCheckerSealFields
  field_faithful := ClosedTypeCheckerSealTasteGate_single_carrier_alignment_fields_faithful

instance closedTypeCheckerSealNontrivial : Nontrivial ClosedTypeCheckerSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedTypeCheckerSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedTypeCheckerSealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ClosedTypeCheckerSealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ClosedTypeCheckerSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedTypeCheckerSealChapterTasteGate

theorem ClosedTypeCheckerSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, closedTypeCheckerSealDecodeBHist (closedTypeCheckerSealEncodeBHist h) = h) ∧
      (∀ x : ClosedTypeCheckerSealUp,
        closedTypeCheckerSealFromEventFlow (closedTypeCheckerSealToEventFlow x) = some x) ∧
        (∀ x y : ClosedTypeCheckerSealUp,
          closedTypeCheckerSealToEventFlow x = closedTypeCheckerSealToEventFlow y → x = y) ∧
          closedTypeCheckerSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨ClosedTypeCheckerSealTasteGate_single_carrier_alignment_decode_encode,
      ClosedTypeCheckerSealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ClosedTypeCheckerSealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ClosedTypeCheckerSealUp
