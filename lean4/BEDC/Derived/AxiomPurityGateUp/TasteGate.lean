import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxiomPurityGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxiomPurityGateUp : Type where
  | mk (T D F R L S H C P N : BHist) : AxiomPurityGateUp
  deriving DecidableEq

def axiomPurityGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axiomPurityGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axiomPurityGateEncodeBHist h

def axiomPurityGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axiomPurityGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axiomPurityGateDecodeBHist tail)

private theorem axiomPurityGateDecode_encode_bhist :
    ∀ h : BHist, axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def axiomPurityGateFields : AxiomPurityGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomPurityGateUp.mk T D F R L S H C P N => [T, D, F, R, L, S, H, C, P, N]

def axiomPurityGateToEventFlow : AxiomPurityGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxiomPurityGateUp.mk T D F R L S H C P N =>
      [[BMark.b0],
        axiomPurityGateEncodeBHist T,
        [BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axiomPurityGateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axiomPurityGateEncodeBHist N]

private def axiomPurityGateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => axiomPurityGateRawAt n rest

private def axiomPurityGateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => axiomPurityGateLengthEq n rest

def axiomPurityGateFromEventFlow : EventFlow → Option AxiomPurityGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match axiomPurityGateLengthEq 20 flow with
      | true =>
          some
            (AxiomPurityGateUp.mk
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 1 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 3 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 5 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 7 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 9 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 11 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 13 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 15 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 17 flow))
              (axiomPurityGateDecodeBHist (axiomPurityGateRawAt 19 flow)))
      | false => none

private theorem axiomPurityGate_round_trip :
    ∀ x : AxiomPurityGateUp,
      axiomPurityGateFromEventFlow (axiomPurityGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T D F R L S H C P N =>
      change
        some
          (AxiomPurityGateUp.mk
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist T))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist D))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist F))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist R))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist L))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist S))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist H))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist C))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist P))
            (axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist N))) =
          some (AxiomPurityGateUp.mk T D F R L S H C P N)
      rw [axiomPurityGateDecode_encode_bhist T,
        axiomPurityGateDecode_encode_bhist D,
        axiomPurityGateDecode_encode_bhist F,
        axiomPurityGateDecode_encode_bhist R,
        axiomPurityGateDecode_encode_bhist L,
        axiomPurityGateDecode_encode_bhist S,
        axiomPurityGateDecode_encode_bhist H,
        axiomPurityGateDecode_encode_bhist C,
        axiomPurityGateDecode_encode_bhist P,
        axiomPurityGateDecode_encode_bhist N]

private theorem axiomPurityGateToEventFlow_injective {x y : AxiomPurityGateUp} :
    axiomPurityGateToEventFlow x = axiomPurityGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axiomPurityGateFromEventFlow (axiomPurityGateToEventFlow x) =
        axiomPurityGateFromEventFlow (axiomPurityGateToEventFlow y) :=
    congrArg axiomPurityGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axiomPurityGate_round_trip x).symm
      (Eq.trans hread (axiomPurityGate_round_trip y)))

private theorem axiomPurityGate_fields_faithful :
    ∀ x y : AxiomPurityGateUp, axiomPurityGateFields x = axiomPurityGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T D F R L S H C P N =>
      cases y with
      | mk T' D' F' R' L' S' H' C' P' N' =>
          cases hfields
          rfl

instance axiomPurityGateBHistCarrier : BHistCarrier AxiomPurityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axiomPurityGateToEventFlow
  fromEventFlow := axiomPurityGateFromEventFlow

instance axiomPurityGateChapterTasteGate : ChapterTasteGate AxiomPurityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axiomPurityGateFromEventFlow (axiomPurityGateToEventFlow x) = some x
    exact axiomPurityGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axiomPurityGateToEventFlow_injective heq)

instance axiomPurityGateFieldFaithful : FieldFaithful AxiomPurityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axiomPurityGateFields
  field_faithful := axiomPurityGate_fields_faithful

instance axiomPurityGateNontrivial : Nontrivial AxiomPurityGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxiomPurityGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AxiomPurityGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxiomPurityGateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axiomPurityGateChapterTasteGate

theorem AxiomPurityGateTasteGate_single_carrier_alignment :
    (∀ h : BHist, axiomPurityGateDecodeBHist (axiomPurityGateEncodeBHist h) = h) ∧
      (∀ x : AxiomPurityGateUp,
        axiomPurityGateFromEventFlow (axiomPurityGateToEventFlow x) = some x) ∧
        (∀ x y : AxiomPurityGateUp,
          axiomPurityGateToEventFlow x = axiomPurityGateToEventFlow y → x = y) ∧
          axiomPurityGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨axiomPurityGateDecode_encode_bhist,
      axiomPurityGate_round_trip,
      (fun _ _ heq => axiomPurityGateToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AxiomPurityGateUp
