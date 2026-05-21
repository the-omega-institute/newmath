import BEDC.Derived.RealUniformStructureUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformStructureUp : Type where
  | mk (R M U F D S Q H C P N : BHist) : RealUniformStructureUp
  deriving DecidableEq

def realUniformStructureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformStructureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformStructureEncodeBHist h

def realUniformStructureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformStructureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformStructureDecodeBHist tail)

private theorem RealUniformStructureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realUniformStructureDecodeBHist (realUniformStructureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformStructureFields : RealUniformStructureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformStructureUp.mk R M U F D S Q H C P N => [R, M, U, F, D, S, Q, H, C, P, N]

def realUniformStructureToEventFlow : RealUniformStructureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => realUniformStructureFields x |>.map realUniformStructureEncodeBHist

private def realUniformStructureRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => realUniformStructureRawAt n rest

def realUniformStructureFromEventFlow (flow : EventFlow) : Option RealUniformStructureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformStructureUp.mk
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 0 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 1 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 2 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 3 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 4 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 5 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 6 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 7 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 8 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 9 flow))
      (realUniformStructureDecodeBHist (realUniformStructureRawAt 10 flow)))

private theorem RealUniformStructureTasteGate_single_carrier_alignment_round_trip
    (x : RealUniformStructureUp) :
    realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R M U F D S Q H C P N =>
      change
        some
          (RealUniformStructureUp.mk
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist R))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist M))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist U))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist F))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist D))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist S))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist Q))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist H))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist C))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist P))
            (realUniformStructureDecodeBHist (realUniformStructureEncodeBHist N))) =
          some (RealUniformStructureUp.mk R M U F D S Q H C P N)
      rw [RealUniformStructureTasteGate_single_carrier_alignment_decode_encode R,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode M,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode U,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode F,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode D,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode S,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode Q,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode H,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode C,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode P,
        RealUniformStructureTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformStructureUp} :
    realUniformStructureToEventFlow x = realUniformStructureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) =
        realUniformStructureFromEventFlow (realUniformStructureToEventFlow y) :=
    congrArg realUniformStructureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealUniformStructureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealUniformStructureTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealUniformStructureTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealUniformStructureUp,
      realUniformStructureFields x = realUniformStructureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ M₁ U₁ F₁ D₁ S₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ M₂ U₂ F₂ D₂ S₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance RealUniformStructureTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformStructureToEventFlow
  fromEventFlow := realUniformStructureFromEventFlow

instance RealUniformStructureTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x
    exact RealUniformStructureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RealUniformStructureTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformStructureFields
  field_faithful := RealUniformStructureTasteGate_single_carrier_alignment_fields_faithful

instance RealUniformStructureTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RealUniformStructureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformStructureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformStructureUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformStructureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealUniformStructureTasteGate_single_carrier_alignment_ChapterTasteGate

theorem RealUniformStructureTasteGate_single_carrier_alignment :
    (∀ h : BHist, realUniformStructureDecodeBHist (realUniformStructureEncodeBHist h) = h) ∧
      (∀ x : RealUniformStructureUp,
        realUniformStructureFromEventFlow (realUniformStructureToEventFlow x) = some x) ∧
      (∀ x y : RealUniformStructureUp,
        realUniformStructureToEventFlow x = realUniformStructureToEventFlow y → x = y) ∧
      realUniformStructureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RealUniformStructureTasteGate_single_carrier_alignment_decode_encode,
      RealUniformStructureTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => RealUniformStructureTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RealUniformStructureUp
