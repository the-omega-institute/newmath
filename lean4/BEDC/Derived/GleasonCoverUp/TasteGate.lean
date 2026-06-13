import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GleasonCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GleasonCoverUp : Type where
  | mk (X E M L B V H C P N : BHist) : GleasonCoverUp

def GleasonCoverTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: GleasonCoverTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: GleasonCoverTasteGate_single_carrier_alignment_encodeBHist h

def GleasonCoverTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem GleasonCoverTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def GleasonCoverTasteGate_single_carrier_alignment_fields : GleasonCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GleasonCoverUp.mk X E M L B V H C P N => [X, E, M, L, B, V, H, C, P, N]

def GleasonCoverTasteGate_single_carrier_alignment_toEventFlow : GleasonCoverUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (GleasonCoverTasteGate_single_carrier_alignment_fields x).map
      GleasonCoverTasteGate_single_carrier_alignment_encodeBHist

private def GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault index rest

def GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option GleasonCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GleasonCoverUp.mk
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
        (GleasonCoverTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem GleasonCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : GleasonCoverUp,
      GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow
        (GleasonCoverTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X E M L B V H C P N =>
      change
        some
          (GleasonCoverUp.mk
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist X))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist E))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist M))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist L))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist B))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist V))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist H))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist C))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist P))
            (GleasonCoverTasteGate_single_carrier_alignment_decodeBHist
              (GleasonCoverTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (GleasonCoverUp.mk X E M L B V H C P N)
      rw [GleasonCoverTasteGate_single_carrier_alignment_decode X,
        GleasonCoverTasteGate_single_carrier_alignment_decode E,
        GleasonCoverTasteGate_single_carrier_alignment_decode M,
        GleasonCoverTasteGate_single_carrier_alignment_decode L,
        GleasonCoverTasteGate_single_carrier_alignment_decode B,
        GleasonCoverTasteGate_single_carrier_alignment_decode V,
        GleasonCoverTasteGate_single_carrier_alignment_decode H,
        GleasonCoverTasteGate_single_carrier_alignment_decode C,
        GleasonCoverTasteGate_single_carrier_alignment_decode P,
        GleasonCoverTasteGate_single_carrier_alignment_decode N]

private theorem GleasonCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GleasonCoverUp} :
    GleasonCoverTasteGate_single_carrier_alignment_toEventFlow x =
      GleasonCoverTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow
          (GleasonCoverTasteGate_single_carrier_alignment_toEventFlow x) =
        GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow
          (GleasonCoverTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GleasonCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GleasonCoverTasteGate_single_carrier_alignment_round_trip y)))

instance gleasonCoverBHistCarrier : BHistCarrier GleasonCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GleasonCoverTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow

instance gleasonCoverChapterTasteGate : ChapterTasteGate GleasonCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      GleasonCoverTasteGate_single_carrier_alignment_fromEventFlow
        (GleasonCoverTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact GleasonCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GleasonCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem GleasonCoverTasteGate_single_carrier_alignment :
    ChapterTasteGate GleasonCoverUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact gleasonCoverChapterTasteGate

end BEDC.Derived.GleasonCoverUp
