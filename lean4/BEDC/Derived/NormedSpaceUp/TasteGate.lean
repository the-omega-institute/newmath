import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormedSpaceUp : Type where
  | mk (V R N M Q H T P C : BHist) : NormedSpaceUp
  deriving DecidableEq

def normedSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normedSpaceEncodeBHist h

def normedSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normedSpaceDecodeBHist tail)

private theorem NormedSpaceUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, normedSpaceDecodeBHist (normedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normedSpaceFields : NormedSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormedSpaceUp.mk V R N M Q H T P C => [V, R, N, M, Q, H, T, P, C]

def normedSpaceToEventFlow : NormedSpaceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (normedSpaceFields x).map normedSpaceEncodeBHist

private def normedSpaceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normedSpaceEventAtDefault index rest

def normedSpaceFromEventFlow (ef : EventFlow) : Option NormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NormedSpaceUp.mk
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 0 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 1 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 2 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 3 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 4 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 5 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 6 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 7 ef))
      (normedSpaceDecodeBHist (normedSpaceEventAtDefault 8 ef)))

private theorem NormedSpaceUpTasteGate_single_carrier_alignment_round_trip :
    forall x : NormedSpaceUp,
      normedSpaceFromEventFlow (normedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk V R N M Q H T P C =>
      change
        some
          (NormedSpaceUp.mk
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist V))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist R))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist N))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist M))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist Q))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist H))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist T))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist P))
            (normedSpaceDecodeBHist (normedSpaceEncodeBHist C))) =
          some (NormedSpaceUp.mk V R N M Q H T P C)
      rw [NormedSpaceUpTasteGate_single_carrier_alignment_decode V,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode R,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode N,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode M,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode Q,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode H,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode T,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode P,
        NormedSpaceUpTasteGate_single_carrier_alignment_decode C]

private theorem NormedSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormedSpaceUp} :
    normedSpaceToEventFlow x = normedSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normedSpaceFromEventFlow (normedSpaceToEventFlow x) =
        normedSpaceFromEventFlow (normedSpaceToEventFlow y) :=
    congrArg normedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NormedSpaceUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NormedSpaceUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem NormedSpaceUpTasteGate_single_carrier_alignment_fields :
    forall x y : NormedSpaceUp, normedSpaceFields x = normedSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 R1 N1 M1 Q1 H1 T1 P1 C1 =>
      cases y with
      | mk V2 R2 N2 M2 Q2 H2 T2 P2 C2 =>
          cases hfields
          rfl

instance normedSpaceBHistCarrier : BHistCarrier NormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normedSpaceToEventFlow
  fromEventFlow := normedSpaceFromEventFlow

instance normedSpaceChapterTasteGate : ChapterTasteGate NormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normedSpaceFromEventFlow (normedSpaceToEventFlow x) = some x
    exact NormedSpaceUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NormedSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance normedSpaceFieldFaithful : FieldFaithful NormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := normedSpaceFields
  field_faithful := NormedSpaceUpTasteGate_single_carrier_alignment_fields

instance normedSpaceNontrivial : Nontrivial NormedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NormedSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NormedSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NormedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normedSpaceChapterTasteGate

theorem NormedSpaceUpTasteGate_single_carrier_alignment :
    (forall h : BHist, normedSpaceDecodeBHist (normedSpaceEncodeBHist h) = h) /\
      (forall x : NormedSpaceUp,
        normedSpaceFromEventFlow (normedSpaceToEventFlow x) = some x) /\
        (forall x y : NormedSpaceUp, normedSpaceToEventFlow x = normedSpaceToEventFlow y -> x = y) /\
          normedSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨NormedSpaceUpTasteGate_single_carrier_alignment_decode,
      NormedSpaceUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => NormedSpaceUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NormedSpaceUp
