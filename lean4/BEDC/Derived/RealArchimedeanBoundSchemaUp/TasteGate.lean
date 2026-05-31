import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArchimedeanBoundSchemaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArchimedeanBoundSchemaUp : Type where
  | mk (R Q D S G B H C P N : BHist) : RealArchimedeanBoundSchemaUp
  deriving DecidableEq

def realArchimedeanBoundSchemaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArchimedeanBoundSchemaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArchimedeanBoundSchemaEncodeBHist h

def realArchimedeanBoundSchemaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArchimedeanBoundSchemaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArchimedeanBoundSchemaDecodeBHist tail)

private theorem realArchimedeanBoundSchema_decode :
    ∀ h : BHist,
      realArchimedeanBoundSchemaDecodeBHist
          (realArchimedeanBoundSchemaEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realArchimedeanBoundSchemaFields :
    RealArchimedeanBoundSchemaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArchimedeanBoundSchemaUp.mk R Q D S G B H C P N =>
      [R, Q, D, S, G, B, H, C, P, N]

def realArchimedeanBoundSchemaToEventFlow :
    RealArchimedeanBoundSchemaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realArchimedeanBoundSchemaFields x).map realArchimedeanBoundSchemaEncodeBHist

private def realArchimedeanBoundSchemaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realArchimedeanBoundSchemaEventAt index rest

def realArchimedeanBoundSchemaFromEventFlow
    (ef : EventFlow) : Option RealArchimedeanBoundSchemaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealArchimedeanBoundSchemaUp.mk
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 0 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 1 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 2 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 3 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 4 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 5 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 6 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 7 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 8 ef))
      (realArchimedeanBoundSchemaDecodeBHist (realArchimedeanBoundSchemaEventAt 9 ef)))

private theorem realArchimedeanBoundSchema_round_trip
    (x : RealArchimedeanBoundSchemaUp) :
    realArchimedeanBoundSchemaFromEventFlow (realArchimedeanBoundSchemaToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R Q D S G B H C P N =>
      change
        some
          (RealArchimedeanBoundSchemaUp.mk
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist R))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist Q))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist D))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist S))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist G))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist B))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist H))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist C))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist P))
            (realArchimedeanBoundSchemaDecodeBHist
              (realArchimedeanBoundSchemaEncodeBHist N))) =
          some (RealArchimedeanBoundSchemaUp.mk R Q D S G B H C P N)
      rw [realArchimedeanBoundSchema_decode R, realArchimedeanBoundSchema_decode Q,
        realArchimedeanBoundSchema_decode D, realArchimedeanBoundSchema_decode S,
        realArchimedeanBoundSchema_decode G, realArchimedeanBoundSchema_decode B,
        realArchimedeanBoundSchema_decode H, realArchimedeanBoundSchema_decode C,
        realArchimedeanBoundSchema_decode P, realArchimedeanBoundSchema_decode N]

private theorem realArchimedeanBoundSchemaToEventFlow_injective
    {x y : RealArchimedeanBoundSchemaUp} :
    realArchimedeanBoundSchemaToEventFlow x = realArchimedeanBoundSchemaToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArchimedeanBoundSchemaFromEventFlow (realArchimedeanBoundSchemaToEventFlow x) =
        realArchimedeanBoundSchemaFromEventFlow
          (realArchimedeanBoundSchemaToEventFlow y) :=
    congrArg realArchimedeanBoundSchemaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realArchimedeanBoundSchema_round_trip x).symm
      (Eq.trans hread (realArchimedeanBoundSchema_round_trip y)))

instance realArchimedeanBoundSchemaBHistCarrier :
    BHistCarrier RealArchimedeanBoundSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArchimedeanBoundSchemaToEventFlow
  fromEventFlow := realArchimedeanBoundSchemaFromEventFlow

instance realArchimedeanBoundSchemaChapterTasteGate :
    ChapterTasteGate RealArchimedeanBoundSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realArchimedeanBoundSchemaFromEventFlow (realArchimedeanBoundSchemaToEventFlow x) =
        some x
    exact realArchimedeanBoundSchema_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realArchimedeanBoundSchemaToEventFlow_injective heq)

instance realArchimedeanBoundSchemaNontrivial :
    Nontrivial RealArchimedeanBoundSchemaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealArchimedeanBoundSchemaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealArchimedeanBoundSchemaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def realArchimedeanBoundSchema_taste_gate :
    ChapterTasteGate RealArchimedeanBoundSchemaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realArchimedeanBoundSchemaChapterTasteGate

theorem RealArchimedeanBoundSchemaTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      UnaryHistory h →
        realArchimedeanBoundSchemaFromEventFlow
            (realArchimedeanBoundSchemaToEventFlow
              (RealArchimedeanBoundSchemaUp.mk h h h h h h h h h h)) =
          some (RealArchimedeanBoundSchemaUp.mk h h h h h h h h h h)) ∧
      (∀ x : RealArchimedeanBoundSchemaUp,
        realArchimedeanBoundSchemaFromEventFlow
            (realArchimedeanBoundSchemaToEventFlow x) =
          some x) ∧
        (∀ x y : RealArchimedeanBoundSchemaUp,
          realArchimedeanBoundSchemaToEventFlow x =
              realArchimedeanBoundSchemaToEventFlow y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  constructor
  · intro h _hUnary
    exact realArchimedeanBoundSchema_round_trip
      (RealArchimedeanBoundSchemaUp.mk h h h h h h h h h h)
  · constructor
    · intro x
      exact realArchimedeanBoundSchema_round_trip x
    · intro x y heq
      exact realArchimedeanBoundSchemaToEventFlow_injective heq

end BEDC.Derived.RealArchimedeanBoundSchemaUp
