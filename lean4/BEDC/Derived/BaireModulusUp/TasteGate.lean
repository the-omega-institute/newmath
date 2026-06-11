import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireModulusUp : Type where
  | mk (prefixRow schedule window modulus handoff : BHist) : BaireModulusUp
  deriving DecidableEq

def baireModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireModulusEncodeBHist h

def baireModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireModulusDecodeBHist tail)

private theorem BaireModulusUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, baireModulusDecodeBHist (baireModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireModulusFields : BaireModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireModulusUp.mk prefixRow schedule window modulus handoff =>
      [prefixRow, schedule, window, modulus, handoff]

def baireModulusToEventFlow : BaireModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (baireModulusFields x).map baireModulusEncodeBHist

private def baireModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireModulusEventAt index rest

def baireModulusFromEventFlow (ef : EventFlow) : Option BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireModulusUp.mk
      (baireModulusDecodeBHist (baireModulusEventAt 0 ef))
      (baireModulusDecodeBHist (baireModulusEventAt 1 ef))
      (baireModulusDecodeBHist (baireModulusEventAt 2 ef))
      (baireModulusDecodeBHist (baireModulusEventAt 3 ef))
      (baireModulusDecodeBHist (baireModulusEventAt 4 ef)))

private theorem BaireModulusUpTasteGate_single_carrier_alignment_round_trip
    (x : BaireModulusUp) :
    baireModulusFromEventFlow (baireModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk prefixRow schedule window modulus handoff =>
      change
        some
          (BaireModulusUp.mk
            (baireModulusDecodeBHist (baireModulusEncodeBHist prefixRow))
            (baireModulusDecodeBHist (baireModulusEncodeBHist schedule))
            (baireModulusDecodeBHist (baireModulusEncodeBHist window))
            (baireModulusDecodeBHist (baireModulusEncodeBHist modulus))
            (baireModulusDecodeBHist (baireModulusEncodeBHist handoff))) =
          some (BaireModulusUp.mk prefixRow schedule window modulus handoff)
      rw [BaireModulusUpTasteGate_single_carrier_alignment_decode_encode prefixRow,
        BaireModulusUpTasteGate_single_carrier_alignment_decode_encode schedule,
        BaireModulusUpTasteGate_single_carrier_alignment_decode_encode window,
        BaireModulusUpTasteGate_single_carrier_alignment_decode_encode modulus,
        BaireModulusUpTasteGate_single_carrier_alignment_decode_encode handoff]

private theorem baireModulusToEventFlow_injective {x y : BaireModulusUp} :
    baireModulusToEventFlow x = baireModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireModulusFromEventFlow (baireModulusToEventFlow x) =
        baireModulusFromEventFlow (baireModulusToEventFlow y) :=
    congrArg baireModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireModulusUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireModulusUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireModulusUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BaireModulusUp, baireModulusFields x = baireModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk prefix1 schedule1 window1 modulus1 handoff1 =>
      cases y with
      | mk prefix2 schedule2 window2 modulus2 handoff2 =>
          cases hfields
          rfl

instance baireModulusBHistCarrier : BHistCarrier BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireModulusToEventFlow
  fromEventFlow := baireModulusFromEventFlow

instance baireModulusChapterTasteGate : ChapterTasteGate BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireModulusFromEventFlow (baireModulusToEventFlow x) = some x
    exact BaireModulusUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (baireModulusToEventFlow_injective heq)

instance baireModulusFieldFaithful : FieldFaithful BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireModulusFields
  field_faithful := BaireModulusUpTasteGate_single_carrier_alignment_fields_faithful

instance baireModulusNontrivial : Nontrivial BaireModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BaireModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  baireModulusChapterTasteGate

theorem BaireModulusUpTasteGate_single_carrier_alignment :
    (∀ x : BaireModulusUp, baireModulusFromEventFlow (baireModulusToEventFlow x) = some x) ∧
      (∀ x y : BaireModulusUp, baireModulusToEventFlow x = baireModulusToEventFlow y → x = y) ∧
      baireModulusFields
          (BaireModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨BaireModulusUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => baireModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BaireModulusUp
