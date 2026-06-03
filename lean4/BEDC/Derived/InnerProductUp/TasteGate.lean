import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InnerProductUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InnerProductUp : Type where
  | mk (V S F A Z L P N : BHist) : InnerProductUp
  deriving DecidableEq

def InnerProductTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: InnerProductTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: InnerProductTasteGate_single_carrier_alignment_encodeBHist h

def InnerProductTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (InnerProductTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (InnerProductTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem InnerProductTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      InnerProductTasteGate_single_carrier_alignment_decodeBHist
        (InnerProductTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def InnerProductTasteGate_single_carrier_alignment_fields : InnerProductUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InnerProductUp.mk V S F A Z L P N => [V, S, F, A, Z, L, P, N]

def InnerProductTasteGate_single_carrier_alignment_toEventFlow : InnerProductUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (InnerProductTasteGate_single_carrier_alignment_fields x).map
        InnerProductTasteGate_single_carrier_alignment_encodeBHist

private def InnerProductTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      InnerProductTasteGate_single_carrier_alignment_eventAt index rest

def InnerProductTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option InnerProductUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (InnerProductUp.mk
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 0 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 1 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 2 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 3 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 4 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 5 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 6 flow))
          (InnerProductTasteGate_single_carrier_alignment_decodeBHist
            (InnerProductTasteGate_single_carrier_alignment_eventAt 7 flow)))

private theorem InnerProductTasteGate_single_carrier_alignment_round_trip :
    forall x : InnerProductUp,
      InnerProductTasteGate_single_carrier_alignment_fromEventFlow
        (InnerProductTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V S F A Z L P N =>
      change
        some
          (InnerProductUp.mk
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist V))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist S))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist F))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist A))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist Z))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist L))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist P))
            (InnerProductTasteGate_single_carrier_alignment_decodeBHist
              (InnerProductTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (InnerProductUp.mk V S F A Z L P N)
      rw [InnerProductTasteGate_single_carrier_alignment_decode V,
        InnerProductTasteGate_single_carrier_alignment_decode S,
        InnerProductTasteGate_single_carrier_alignment_decode F,
        InnerProductTasteGate_single_carrier_alignment_decode A,
        InnerProductTasteGate_single_carrier_alignment_decode Z,
        InnerProductTasteGate_single_carrier_alignment_decode L,
        InnerProductTasteGate_single_carrier_alignment_decode P,
        InnerProductTasteGate_single_carrier_alignment_decode N]

private theorem InnerProductTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : InnerProductUp} :
    InnerProductTasteGate_single_carrier_alignment_toEventFlow x =
      InnerProductTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      InnerProductTasteGate_single_carrier_alignment_fromEventFlow
          (InnerProductTasteGate_single_carrier_alignment_toEventFlow x) =
        InnerProductTasteGate_single_carrier_alignment_fromEventFlow
          (InnerProductTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg InnerProductTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InnerProductTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (InnerProductTasteGate_single_carrier_alignment_round_trip y)))

private theorem InnerProductTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : InnerProductUp,
      InnerProductTasteGate_single_carrier_alignment_fields x =
        InnerProductTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 S1 F1 A1 Z1 L1 P1 N1 =>
      cases y with
      | mk V2 S2 F2 A2 Z2 L2 P2 N2 =>
          cases hfields
          rfl

instance innerProductBHistCarrier : BHistCarrier InnerProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := InnerProductTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := InnerProductTasteGate_single_carrier_alignment_fromEventFlow

instance innerProductChapterTasteGate : ChapterTasteGate InnerProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      InnerProductTasteGate_single_carrier_alignment_fromEventFlow
        (InnerProductTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact InnerProductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InnerProductTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance innerProductFieldFaithful : FieldFaithful InnerProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := InnerProductTasteGate_single_carrier_alignment_fields
  field_faithful := InnerProductTasteGate_single_carrier_alignment_fields_faithful

instance innerProductNontrivial : Nontrivial InnerProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InnerProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      InnerProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem InnerProductTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate InnerProductUp) /\
      (forall x : InnerProductUp,
        exists e : EventFlow, BHistCarrier.fromEventFlow e = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨innerProductChapterTasteGate⟩
  · intro x
    exact
      ⟨InnerProductTasteGate_single_carrier_alignment_toEventFlow x,
        ChapterTasteGate.round_trip x⟩

end BEDC.Derived.InnerProductUp.TasteGate
