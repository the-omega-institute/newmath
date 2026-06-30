import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalHalvingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalHalvingUp : Type where
  | mk (L R M B ρ S Q E T C P N : BHist) : IntervalHalvingUp
  deriving DecidableEq

def IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist h

def IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem IntervalHalvingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
          (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def IntervalHalvingTasteGate_single_carrier_alignment_fields :
    IntervalHalvingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalHalvingUp.mk L R M B ρ S Q E T C P N => [L, R, M, B, ρ, S, Q, E, T, C, P, N]

def IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow :
    IntervalHalvingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (IntervalHalvingTasteGate_single_carrier_alignment_fields x).map
      IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist

private def IntervalHalvingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IntervalHalvingTasteGate_single_carrier_alignment_eventAt index rest

def IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option IntervalHalvingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalHalvingUp.mk
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 0 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 1 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 2 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 3 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 4 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 5 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 6 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 7 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 8 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 9 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 10 ef))
      (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
        (IntervalHalvingTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem IntervalHalvingTasteGate_single_carrier_alignment_round_trip
    (x : IntervalHalvingUp) :
    IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow
        (IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L R M B ρ S Q E T C P N =>
      change
        some
            (IntervalHalvingUp.mk
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist L))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist R))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist M))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist B))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist ρ))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist S))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist Q))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist E))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist T))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist C))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist P))
              (IntervalHalvingTasteGate_single_carrier_alignment_decodeBHist
                (IntervalHalvingTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (IntervalHalvingUp.mk L R M B ρ S Q E T C P N)
      rw [IntervalHalvingTasteGate_single_carrier_alignment_decode L,
        IntervalHalvingTasteGate_single_carrier_alignment_decode R,
        IntervalHalvingTasteGate_single_carrier_alignment_decode M,
        IntervalHalvingTasteGate_single_carrier_alignment_decode B,
        IntervalHalvingTasteGate_single_carrier_alignment_decode ρ,
        IntervalHalvingTasteGate_single_carrier_alignment_decode S,
        IntervalHalvingTasteGate_single_carrier_alignment_decode Q,
        IntervalHalvingTasteGate_single_carrier_alignment_decode E,
        IntervalHalvingTasteGate_single_carrier_alignment_decode T,
        IntervalHalvingTasteGate_single_carrier_alignment_decode C,
        IntervalHalvingTasteGate_single_carrier_alignment_decode P,
        IntervalHalvingTasteGate_single_carrier_alignment_decode N]

private theorem IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntervalHalvingUp} :
    IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow x =
        IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow x) =
        IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntervalHalvingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalHalvingTasteGate_single_carrier_alignment_round_trip y)))

instance intervalHalvingTasteGate_single_carrier_alignmentBHistCarrier :
    BHistCarrier IntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow

instance intervalHalvingTasteGate_single_carrier_alignmentChapterTasteGate :
    ChapterTasteGate IntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntervalHalvingTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact IntervalHalvingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem IntervalHalvingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate IntervalHalvingUp) ∧
      (∀ x : IntervalHalvingUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨intervalHalvingTasteGate_single_carrier_alignmentChapterTasteGate⟩
  · intro x
    exact
      ⟨IntervalHalvingTasteGate_single_carrier_alignment_toEventFlow x,
        IntervalHalvingTasteGate_single_carrier_alignment_round_trip x⟩

end BEDC.Derived.IntervalHalvingUp.TasteGate
