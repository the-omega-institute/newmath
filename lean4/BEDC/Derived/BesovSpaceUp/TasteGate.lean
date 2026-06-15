import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BesovSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BesovSpaceUp : Type where
  | mk : (S Hd W R Q D E T C P N : BHist) → BesovSpaceUp
  deriving DecidableEq

def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

def decodeBHist : RawEvent → Option BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some BHist.Empty
  | BMark.b0 :: tail =>
      match decodeBHist tail with
      | some h => some (BHist.e0 h)
      | none => none
  | BMark.b1 :: tail =>
      match decodeBHist tail with
      | some h => some (BHist.e1 h)
      | none => none

private def BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal tail)

theorem BesovSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ w : BHist, decodeBHist (encodeBHist w) = some w := by
  -- BEDC touchpoint anchor: BHist BMark
  intro w
  induction w with
  | Empty => rfl
  | e0 h ih =>
      change
        (match decodeBHist (encodeBHist h) with
        | some h => some (BHist.e0 h)
        | none => none) = some (BHist.e0 h)
      rw [ih]
  | e1 h ih =>
      change
        (match decodeBHist (encodeBHist h) with
        | some h => some (BHist.e1 h)
        | none => none) = some (BHist.e1 h)
      rw [ih]

private theorem BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode :
    ∀ w : BHist,
      BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist w) = w := by
  -- BEDC touchpoint anchor: BHist BMark
  intro w
  induction w with
  | Empty => rfl
  | e0 h ih =>
      change
        BHist.e0 (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (encodeBHist h)) = BHist.e0 h
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      change
        BHist.e1 (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (encodeBHist h)) = BHist.e1 h
      exact congrArg BHist.e1 ih

def besovSpaceFields : BesovSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BesovSpaceUp.mk S Hd W R Q D E T C P N => [S, Hd, W, R, Q, D, E, T, C, P, N]

def besovSpaceToEventFlow : BesovSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BesovSpaceUp.mk S Hd W R Q D E T C P N =>
      [encodeBHist S, encodeBHist Hd, encodeBHist W, encodeBHist R, encodeBHist Q,
        encodeBHist D, encodeBHist E, encodeBHist T, encodeBHist C, encodeBHist P,
        encodeBHist N]

private def besovSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => besovSpaceEventAtDefault index rest

def besovSpaceFromEventFlow : EventFlow → Option BesovSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BesovSpaceUp.mk
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 0 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 1 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 2 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 3 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 4 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 5 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 6 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 7 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 8 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 9 ef))
        (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal
          (besovSpaceEventAtDefault 10 ef)))

private theorem BesovSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BesovSpaceUp, besovSpaceFromEventFlow (besovSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Hd W R Q D E T C P N =>
      change
        some
            (BesovSpaceUp.mk
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist S))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist Hd))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist W))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist R))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist Q))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist D))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist E))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist T))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist C))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist P))
              (BesovSpaceTasteGate_single_carrier_alignment_decodeBHistTotal (encodeBHist N))) =
          some (BesovSpaceUp.mk S Hd W R Q D E T C P N)
      rw [BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode S,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode Hd,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode W,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode R,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode Q,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode D,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode E,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode T,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode C,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode P,
        BesovSpaceTasteGate_single_carrier_alignment_total_decode_encode N]

private theorem BesovSpaceTasteGate_single_carrier_alignment_injective {x y : BesovSpaceUp} :
    besovSpaceToEventFlow x = besovSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      besovSpaceFromEventFlow (besovSpaceToEventFlow x) =
        besovSpaceFromEventFlow (besovSpaceToEventFlow y) :=
    congrArg besovSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BesovSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BesovSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem besovSpace_field_faithful :
    ∀ x y : BesovSpaceUp, besovSpaceFields x = besovSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ Hd₁ W₁ R₁ Q₁ D₁ E₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Hd₂ W₂ R₂ Q₂ D₂ E₂ T₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance besovSpaceBHistCarrier : BHistCarrier BesovSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := besovSpaceToEventFlow
  fromEventFlow := besovSpaceFromEventFlow

instance besovSpaceChapterTasteGate : ChapterTasteGate BesovSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change besovSpaceFromEventFlow (besovSpaceToEventFlow x) = some x
    exact BesovSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BesovSpaceTasteGate_single_carrier_alignment_injective heq)

instance besovSpaceFieldFaithful : FieldFaithful BesovSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := besovSpaceFields
  field_faithful := besovSpace_field_faithful

instance besovSpaceInhabited : Inhabited BesovSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    BesovSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

instance besovSpaceNontrivial : Nontrivial BesovSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BesovSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BesovSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BesovSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  besovSpaceChapterTasteGate

theorem BesovSpaceTasteGate_single_carrier_alignment :
    (∀ w : BHist, decodeBHist (encodeBHist w) = some w) ∧
      besovSpaceToEventFlow
          (BesovSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty,
          encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty,
          encodeBHist BHist.Empty, encodeBHist BHist.Empty, encodeBHist BHist.Empty,
          encodeBHist BHist.Empty, encodeBHist BHist.Empty] ∧
      (∀ x : BesovSpaceUp, besovSpaceFromEventFlow (besovSpaceToEventFlow x) = some x) ∧
      (∀ x y : BesovSpaceUp, besovSpaceFields x = besovSpaceFields y → x = y) ∧
      (besovSpaceFields
          (BesovSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)).length =
        11 := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact BesovSpaceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · constructor
      · exact BesovSpaceTasteGate_single_carrier_alignment_round_trip
      · constructor
        · exact besovSpace_field_faithful
        · rfl

end BEDC.Derived.BesovSpaceUp
