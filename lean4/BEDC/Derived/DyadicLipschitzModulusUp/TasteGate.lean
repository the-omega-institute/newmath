import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicLipschitzModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicLipschitzModulusUp : Type where
  | mk (D S R B G H C P N : BHist) : DyadicLipschitzModulusUp
  deriving DecidableEq

def dyadicLipschitzModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicLipschitzModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicLipschitzModulusEncodeBHist h

def dyadicLipschitzModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicLipschitzModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicLipschitzModulusDecodeBHist tail)

private theorem DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicLipschitzModulusDecodeBHist
        (dyadicLipschitzModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicLipschitzModulusFields : DyadicLipschitzModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicLipschitzModulusUp.mk D S R B G H C P N => [D, S, R, B, G, H, C, P, N]

def dyadicLipschitzModulusToEventFlow : DyadicLipschitzModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicLipschitzModulusFields x).map dyadicLipschitzModulusEncodeBHist

private def dyadicLipschitzModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicLipschitzModulusEventAt index rest

def dyadicLipschitzModulusFromEventFlow (ef : EventFlow) :
    Option DyadicLipschitzModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicLipschitzModulusUp.mk
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 0 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 1 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 2 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 3 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 4 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 5 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 6 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 7 ef))
      (dyadicLipschitzModulusDecodeBHist (dyadicLipschitzModulusEventAt 8 ef)))

private theorem DyadicLipschitzModulusTasteGate_single_carrier_alignment_round_trip
    (x : DyadicLipschitzModulusUp) :
    dyadicLipschitzModulusFromEventFlow
      (dyadicLipschitzModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R B G H C P N =>
      change
        some
          (DyadicLipschitzModulusUp.mk
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist D))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist S))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist R))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist B))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist G))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist H))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist C))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist P))
            (dyadicLipschitzModulusDecodeBHist
              (dyadicLipschitzModulusEncodeBHist N))) =
          some (DyadicLipschitzModulusUp.mk D S R B G H C P N)
      rw [DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode D,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode S,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode R,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode B,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode G,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode H,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode C,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode P,
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicLipschitzModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicLipschitzModulusUp} :
    dyadicLipschitzModulusToEventFlow x =
      dyadicLipschitzModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicLipschitzModulusFromEventFlow (dyadicLipschitzModulusToEventFlow x) =
        dyadicLipschitzModulusFromEventFlow (dyadicLipschitzModulusToEventFlow y) :=
    congrArg dyadicLipschitzModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicLipschitzModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicLipschitzModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicLipschitzModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DyadicLipschitzModulusUp,
      dyadicLipschitzModulusFields x = dyadicLipschitzModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ B₁ G₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ B₂ G₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicLipschitzModulusBHistCarrier : BHistCarrier DyadicLipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicLipschitzModulusToEventFlow
  fromEventFlow := dyadicLipschitzModulusFromEventFlow

instance dyadicLipschitzModulusChapterTasteGate :
    ChapterTasteGate DyadicLipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicLipschitzModulusFromEventFlow (dyadicLipschitzModulusToEventFlow x) =
        some x
    exact DyadicLipschitzModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicLipschitzModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicLipschitzModulusFieldFaithful :
    FieldFaithful DyadicLipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicLipschitzModulusFields
  field_faithful :=
    DyadicLipschitzModulusTasteGate_single_carrier_alignment_fields_faithful

instance dyadicLipschitzModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicLipschitzModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicLipschitzModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicLipschitzModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DyadicLipschitzModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicLipschitzModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicLipschitzModulusChapterTasteGate

theorem DyadicLipschitzModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicLipschitzModulusUp) ∧
      Nonempty (FieldFaithful DyadicLipschitzModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicLipschitzModulusUp) ∧
      (∀ h : BHist,
        dyadicLipschitzModulusDecodeBHist
          (dyadicLipschitzModulusEncodeBHist h) = h) ∧
      (∀ x : DyadicLipschitzModulusUp,
        dyadicLipschitzModulusFromEventFlow
          (dyadicLipschitzModulusToEventFlow x) = some x) ∧
      (∀ x y : DyadicLipschitzModulusUp,
        dyadicLipschitzModulusToEventFlow x =
          dyadicLipschitzModulusToEventFlow y → x = y) ∧
      dyadicLipschitzModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨dyadicLipschitzModulusChapterTasteGate⟩,
      ⟨dyadicLipschitzModulusFieldFaithful⟩,
      ⟨dyadicLipschitzModulusNontrivial⟩,
      DyadicLipschitzModulusTasteGate_single_carrier_alignment_decode_encode,
      DyadicLipschitzModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicLipschitzModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicLipschitzModulusUp
