import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealApartnessOrderBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealApartnessOrderBridgeUp : Type where
  | mk (X Y A L R D S H C P N : BHist) : RealApartnessOrderBridgeUp
  deriving DecidableEq

def realApartnessOrderBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realApartnessOrderBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realApartnessOrderBridgeEncodeBHist h

def realApartnessOrderBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realApartnessOrderBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realApartnessOrderBridgeDecodeBHist tail)

private theorem RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realApartnessOrderBridgeFields : RealApartnessOrderBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealApartnessOrderBridgeUp.mk X Y A L R D S H C P N =>
      [X, Y, A, L, R, D, S, H, C, P, N]

def realApartnessOrderBridgeToEventFlow : RealApartnessOrderBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realApartnessOrderBridgeFields x).map realApartnessOrderBridgeEncodeBHist

private def RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt index rest

def realApartnessOrderBridgeFromEventFlow
    (ef : EventFlow) : Option RealApartnessOrderBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealApartnessOrderBridgeUp.mk
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 0 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 1 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 2 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 3 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 4 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 5 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 6 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 7 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 8 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 9 ef))
      (realApartnessOrderBridgeDecodeBHist
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem RealApartnessOrderBridgeTasteGate_single_carrier_alignment_round_trip
    (x : RealApartnessOrderBridgeUp) :
    realApartnessOrderBridgeFromEventFlow (realApartnessOrderBridgeToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y A L R D S H C P N =>
      change
        some
          (RealApartnessOrderBridgeUp.mk
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist X))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist Y))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist A))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist L))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist R))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist D))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist S))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist H))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist C))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist P))
            (realApartnessOrderBridgeDecodeBHist (realApartnessOrderBridgeEncodeBHist N))) =
          some (RealApartnessOrderBridgeUp.mk X Y A L R D S H C P N)
      rw [RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode X,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode Y,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode A,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode L,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode R,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode D,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode S,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode H,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode C,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode P,
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealApartnessOrderBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealApartnessOrderBridgeUp} :
    realApartnessOrderBridgeToEventFlow x = realApartnessOrderBridgeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realApartnessOrderBridgeFromEventFlow (realApartnessOrderBridgeToEventFlow x) =
        realApartnessOrderBridgeFromEventFlow (realApartnessOrderBridgeToEventFlow y) :=
    congrArg realApartnessOrderBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealApartnessOrderBridgeTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealApartnessOrderBridgeUp,
      realApartnessOrderBridgeFields x = realApartnessOrderBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Y₁ A₁ L₁ R₁ D₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Y₂ A₂ L₂ R₂ D₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realApartnessOrderBridgeBHistCarrier : BHistCarrier RealApartnessOrderBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realApartnessOrderBridgeToEventFlow
  fromEventFlow := realApartnessOrderBridgeFromEventFlow

instance realApartnessOrderBridgeChapterTasteGate :
    ChapterTasteGate RealApartnessOrderBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realApartnessOrderBridgeFromEventFlow (realApartnessOrderBridgeToEventFlow x) =
        some x
    exact RealApartnessOrderBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealApartnessOrderBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realApartnessOrderBridgeFieldFaithful :
    FieldFaithful RealApartnessOrderBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realApartnessOrderBridgeFields
  field_faithful := RealApartnessOrderBridgeTasteGate_single_carrier_alignment_fields_faithful

instance realApartnessOrderBridgeNontrivial : Nontrivial RealApartnessOrderBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealApartnessOrderBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealApartnessOrderBridgeUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealApartnessOrderBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realApartnessOrderBridgeChapterTasteGate

theorem RealApartnessOrderBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, realApartnessOrderBridgeDecodeBHist
      (realApartnessOrderBridgeEncodeBHist h) = h) ∧
      (∀ x : RealApartnessOrderBridgeUp,
        realApartnessOrderBridgeFromEventFlow (realApartnessOrderBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : RealApartnessOrderBridgeUp,
          realApartnessOrderBridgeToEventFlow x =
            realApartnessOrderBridgeToEventFlow y -> x = y) ∧
          realApartnessOrderBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨RealApartnessOrderBridgeTasteGate_single_carrier_alignment_decode_encode,
      RealApartnessOrderBridgeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealApartnessOrderBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealApartnessOrderBridgeUp
