import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AscoliDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AscoliDiagonalUp : Type where
  | mk (X E Y W R S H C P N : BHist) : AscoliDiagonalUp
  deriving DecidableEq

def ascoliDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ascoliDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: ascoliDiagonalEncodeBHist h

def ascoliDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ascoliDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ascoliDiagonalDecodeBHist tail)

private theorem AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ascoliDiagonalFields : AscoliDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AscoliDiagonalUp.mk X E Y W R S H C P N => [X, E, Y, W, R, S, H, C, P, N]

def ascoliDiagonalToEventFlow : AscoliDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (ascoliDiagonalFields x).map ascoliDiagonalEncodeBHist

private def ascoliDiagonalEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ascoliDiagonalEventAt index rest

def ascoliDiagonalFromEventFlow (ef : EventFlow) : Option AscoliDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AscoliDiagonalUp.mk
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 0 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 1 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 2 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 3 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 4 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 5 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 6 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 7 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 8 ef))
      (ascoliDiagonalDecodeBHist (ascoliDiagonalEventAt 9 ef)))

private theorem AscoliDiagonalTasteGate_single_carrier_alignment_round_trip
    (x : AscoliDiagonalUp) :
    ascoliDiagonalFromEventFlow (ascoliDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X E Y W R S H C P N =>
      change
        some
          (AscoliDiagonalUp.mk
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist X))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist E))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist Y))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist W))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist R))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist S))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist H))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist C))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist P))
            (ascoliDiagonalDecodeBHist (ascoliDiagonalEncodeBHist N))) =
          some (AscoliDiagonalUp.mk X E Y W R S H C P N)
      rw [AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode X,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode E,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode Y,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode W,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode R,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode S,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode H,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode C,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode P,
        AscoliDiagonalTasteGate_single_carrier_alignment_decode_encode N]

private theorem AscoliDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AscoliDiagonalUp} :
    ascoliDiagonalToEventFlow x = ascoliDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ascoliDiagonalFromEventFlow (ascoliDiagonalToEventFlow x) =
        ascoliDiagonalFromEventFlow (ascoliDiagonalToEventFlow y) :=
    congrArg ascoliDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AscoliDiagonalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AscoliDiagonalTasteGate_single_carrier_alignment_round_trip y)))

private theorem AscoliDiagonalTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AscoliDiagonalUp, ascoliDiagonalFields x = ascoliDiagonalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ E₁ Y₁ W₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ E₂ Y₂ W₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance ascoliDiagonalBHistCarrier : BHistCarrier AscoliDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ascoliDiagonalToEventFlow
  fromEventFlow := ascoliDiagonalFromEventFlow

instance ascoliDiagonalChapterTasteGate : ChapterTasteGate AscoliDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change ascoliDiagonalFromEventFlow (ascoliDiagonalToEventFlow x) = some x
    exact AscoliDiagonalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AscoliDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ascoliDiagonalFieldFaithful : FieldFaithful AscoliDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ascoliDiagonalFields
  field_faithful := AscoliDiagonalTasteGate_single_carrier_alignment_fields_faithful

instance ascoliDiagonalNontrivial : Nontrivial AscoliDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AscoliDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AscoliDiagonalUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def AscoliDiagonalTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate AscoliDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ascoliDiagonalChapterTasteGate

theorem AscoliDiagonalTasteGate_single_carrier_alignment :
    ChapterTasteGate AscoliDiagonalUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ascoliDiagonalChapterTasteGate

end BEDC.Derived.AscoliDiagonalUp
