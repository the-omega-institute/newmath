import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScottRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScottRealUp : Type where
  | mk (I W D M R E H C P N : BHist) : ScottRealUp
  deriving DecidableEq

def ScottRealTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ScottRealTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ScottRealTasteGate_single_carrier_alignment_encodeBHist h

def ScottRealTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ScottRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ScottRealTasteGate_single_carrier_alignment_decodeBHist
          (ScottRealTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ScottRealTasteGate_single_carrier_alignment_fields : ScottRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScottRealUp.mk I W D M R E H C P N => [I, W, D, M, R, E, H, C, P, N]

def ScottRealTasteGate_single_carrier_alignment_toEventFlow : ScottRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (ScottRealTasteGate_single_carrier_alignment_fields x).map
      ScottRealTasteGate_single_carrier_alignment_encodeBHist

private def ScottRealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => ScottRealTasteGate_single_carrier_alignment_eventAt index rest

def ScottRealTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option ScottRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ScottRealUp.mk
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 7 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 8 ef))
      (ScottRealTasteGate_single_carrier_alignment_decodeBHist
        (ScottRealTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem ScottRealTasteGate_single_carrier_alignment_round_trip
    (x : ScottRealUp) :
    ScottRealTasteGate_single_carrier_alignment_fromEventFlow
        (ScottRealTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I W D M R E H C P N =>
      change
        some
          (ScottRealUp.mk
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist I))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist W))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist D))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist M))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist R))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist E))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist H))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist C))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist P))
            (ScottRealTasteGate_single_carrier_alignment_decodeBHist
              (ScottRealTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ScottRealUp.mk I W D M R E H C P N)
      rw [ScottRealTasteGate_single_carrier_alignment_decode_encode I,
        ScottRealTasteGate_single_carrier_alignment_decode_encode W,
        ScottRealTasteGate_single_carrier_alignment_decode_encode D,
        ScottRealTasteGate_single_carrier_alignment_decode_encode M,
        ScottRealTasteGate_single_carrier_alignment_decode_encode R,
        ScottRealTasteGate_single_carrier_alignment_decode_encode E,
        ScottRealTasteGate_single_carrier_alignment_decode_encode H,
        ScottRealTasteGate_single_carrier_alignment_decode_encode C,
        ScottRealTasteGate_single_carrier_alignment_decode_encode P,
        ScottRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem ScottRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ScottRealUp} :
    ScottRealTasteGate_single_carrier_alignment_toEventFlow x =
        ScottRealTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ScottRealTasteGate_single_carrier_alignment_fromEventFlow
          (ScottRealTasteGate_single_carrier_alignment_toEventFlow x) =
        ScottRealTasteGate_single_carrier_alignment_fromEventFlow
          (ScottRealTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ScottRealTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ScottRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ScottRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem ScottRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ScottRealUp,
      ScottRealTasteGate_single_carrier_alignment_fields x =
          ScottRealTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ W₁ D₁ M₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ W₂ D₂ M₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance ScottRealTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ScottRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ScottRealTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ScottRealTasteGate_single_carrier_alignment_fromEventFlow

instance ScottRealTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ScottRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ScottRealTasteGate_single_carrier_alignment_fromEventFlow
          (ScottRealTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact ScottRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ScottRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance ScottRealTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful ScottRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ScottRealTasteGate_single_carrier_alignment_fields
  field_faithful := ScottRealTasteGate_single_carrier_alignment_fields_faithful

def ScottRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ScottRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ScottRealTasteGate_single_carrier_alignment_ChapterTasteGate

theorem ScottRealTasteGate_single_carrier_alignment : ChapterTasteGate ScottRealUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ScottRealTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.ScottRealUp
