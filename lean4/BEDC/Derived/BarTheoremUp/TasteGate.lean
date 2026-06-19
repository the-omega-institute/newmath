import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BarTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BarTheoremUp : Type where
  | mk (T B R F S C H K P N : BHist) : BarTheoremUp
  deriving DecidableEq

def BarTheoremTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BarTheoremTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BarTheoremTasteGate_single_carrier_alignment_encodeBHist h

def BarTheoremTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (BarTheoremTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (BarTheoremTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BarTheoremTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BarTheoremTasteGate_single_carrier_alignment_fields : BarTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BarTheoremUp.mk T B R F S C H K P N => [T, B, R, F, S, C, H, K, P, N]

def BarTheoremTasteGate_single_carrier_alignment_toEventFlow : BarTheoremUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BarTheoremTasteGate_single_carrier_alignment_fields x).map
      BarTheoremTasteGate_single_carrier_alignment_encodeBHist

private def BarTheoremTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BarTheoremTasteGate_single_carrier_alignment_eventAt index rest

def BarTheoremTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BarTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BarTheoremUp.mk
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 0 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 1 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 2 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 3 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 4 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 5 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 6 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 7 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 8 ef))
      (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
        (BarTheoremTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem BarTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BarTheoremUp,
      BarTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (BarTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T B R F S C H K P N =>
      change
        some
          (BarTheoremUp.mk
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist T))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist B))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist R))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist F))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist S))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist C))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist H))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist K))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist P))
            (BarTheoremTasteGate_single_carrier_alignment_decodeBHist
              (BarTheoremTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BarTheoremUp.mk T B R F S C H K P N)
      rw [BarTheoremTasteGate_single_carrier_alignment_decode T,
        BarTheoremTasteGate_single_carrier_alignment_decode B,
        BarTheoremTasteGate_single_carrier_alignment_decode R,
        BarTheoremTasteGate_single_carrier_alignment_decode F,
        BarTheoremTasteGate_single_carrier_alignment_decode S,
        BarTheoremTasteGate_single_carrier_alignment_decode C,
        BarTheoremTasteGate_single_carrier_alignment_decode H,
        BarTheoremTasteGate_single_carrier_alignment_decode K,
        BarTheoremTasteGate_single_carrier_alignment_decode P,
        BarTheoremTasteGate_single_carrier_alignment_decode N]

private theorem BarTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BarTheoremUp} :
    BarTheoremTasteGate_single_carrier_alignment_toEventFlow x =
      BarTheoremTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BarTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (BarTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        BarTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (BarTheoremTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BarTheoremTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BarTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BarTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance barTheoremBHistCarrier : BHistCarrier BarTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BarTheoremTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BarTheoremTasteGate_single_carrier_alignment_fromEventFlow

instance barTheoremChapterTasteGate : ChapterTasteGate BarTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BarTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (BarTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact BarTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BarTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BarTheoremTasteGate_single_carrier_alignment :
    (∀ T B R F S C H K P N : BHist,
      BarTheoremTasteGate_single_carrier_alignment_fields
        (BarTheoremUp.mk T B R F S C H K P N) =
        [T, B, R, F, S, C, H, K, P, N]) ∧
      (∀ h : BHist,
        BarTheoremTasteGate_single_carrier_alignment_decodeBHist
          (BarTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        BarTheoremTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(by intro T B R F S C H K P N; rfl),
      BarTheoremTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.BarTheoremUp
