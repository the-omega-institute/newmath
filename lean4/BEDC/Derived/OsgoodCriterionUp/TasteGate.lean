import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OsgoodCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OsgoodCriterionUp : Type where
  | mk (D I V M B Q R E H C P N : BHist) : OsgoodCriterionUp
  deriving DecidableEq

def OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist h

def OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem OsgoodCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
          (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def OsgoodCriterionTasteGate_single_carrier_alignment_fields :
    OsgoodCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OsgoodCriterionUp.mk D I V M B Q R E H C P N => [D, I, V, M, B, Q, R, E, H, C, P, N]

def OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow :
    OsgoodCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (OsgoodCriterionTasteGate_single_carrier_alignment_fields x).map
      OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist

private def OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault index rest

def OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option OsgoodCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OsgoodCriterionUp.mk
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
        (OsgoodCriterionTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem OsgoodCriterionTasteGate_single_carrier_alignment_round_trip
    (x : OsgoodCriterionUp) :
    OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow
        (OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D I V M B Q R E H C P N =>
      change
        some
            (OsgoodCriterionUp.mk
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist D))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist I))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist V))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist M))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist B))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist Q))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist R))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist E))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist H))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist C))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist P))
              (OsgoodCriterionTasteGate_single_carrier_alignment_decodeBHist
                (OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (OsgoodCriterionUp.mk D I V M B Q R E H C P N)
      rw [OsgoodCriterionTasteGate_single_carrier_alignment_decode D,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode I,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode V,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode M,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode B,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode Q,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode R,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode E,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode H,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode C,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode P,
        OsgoodCriterionTasteGate_single_carrier_alignment_decode N]

private theorem OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OsgoodCriterionUp} :
    OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow x =
        OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OsgoodCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OsgoodCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance osgoodCriterionBHistCarrier : BHistCarrier OsgoodCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow

instance osgoodCriterionChapterTasteGate : ChapterTasteGate OsgoodCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      OsgoodCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact OsgoodCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OsgoodCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate OsgoodCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  osgoodCriterionChapterTasteGate

theorem OsgoodCriterionTasteGate_single_carrier_alignment :
    (∀ D I V M B Q R E H C P N : BHist,
      OsgoodCriterionTasteGate_single_carrier_alignment_fields
          (OsgoodCriterionUp.mk D I V M B Q R E H C P N) =
        [D, I, V, M, B, Q, R, E, H, C, P, N]) ∧
      OsgoodCriterionTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.OsgoodCriterionUp.TasteGate
