import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GronwallBellmanUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GronwallBellmanUp : Type where
  | mk (I K M P E R Z H C Q N : BHist) : GronwallBellmanUp
  deriving DecidableEq

def GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist h

def GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem GronwallBellmanTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
        (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def GronwallBellmanTasteGate_single_carrier_alignment_fields :
    GronwallBellmanUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GronwallBellmanUp.mk I K M P E R Z H C Q N => [I, K, M, P, E, R, Z, H, C, Q, N]

def GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow :
    GronwallBellmanUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (GronwallBellmanTasteGate_single_carrier_alignment_fields x).map
        GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist

private def GronwallBellmanTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      GronwallBellmanTasteGate_single_carrier_alignment_eventAt index rest

def GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option GronwallBellmanUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (GronwallBellmanUp.mk
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 0 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 1 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 2 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 3 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 4 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 5 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 6 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 7 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 8 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 9 flow))
          (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
            (GronwallBellmanTasteGate_single_carrier_alignment_eventAt 10 flow)))

private theorem GronwallBellmanTasteGate_single_carrier_alignment_round_trip :
    forall x : GronwallBellmanUp,
      GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow
        (GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I K M P E R Z H C Q N =>
      change
        some
          (GronwallBellmanUp.mk
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist I))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist K))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist M))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist P))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist E))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist R))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist Z))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist H))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist C))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist Q))
            (GronwallBellmanTasteGate_single_carrier_alignment_decodeBHist
              (GronwallBellmanTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (GronwallBellmanUp.mk I K M P E R Z H C Q N)
      rw [GronwallBellmanTasteGate_single_carrier_alignment_decode I,
        GronwallBellmanTasteGate_single_carrier_alignment_decode K,
        GronwallBellmanTasteGate_single_carrier_alignment_decode M,
        GronwallBellmanTasteGate_single_carrier_alignment_decode P,
        GronwallBellmanTasteGate_single_carrier_alignment_decode E,
        GronwallBellmanTasteGate_single_carrier_alignment_decode R,
        GronwallBellmanTasteGate_single_carrier_alignment_decode Z,
        GronwallBellmanTasteGate_single_carrier_alignment_decode H,
        GronwallBellmanTasteGate_single_carrier_alignment_decode C,
        GronwallBellmanTasteGate_single_carrier_alignment_decode Q,
        GronwallBellmanTasteGate_single_carrier_alignment_decode N]

private theorem GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GronwallBellmanUp} :
    GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow x =
      GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow
          (GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow x) =
        GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow
          (GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GronwallBellmanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GronwallBellmanTasteGate_single_carrier_alignment_round_trip y)))

private theorem GronwallBellmanTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : GronwallBellmanUp,
      GronwallBellmanTasteGate_single_carrier_alignment_fields x =
        GronwallBellmanTasteGate_single_carrier_alignment_fields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 K1 M1 P1 E1 R1 Z1 H1 C1 Q1 N1 =>
      cases y with
      | mk I2 K2 M2 P2 E2 R2 Z2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance gronwallBellmanBHistCarrier : BHistCarrier GronwallBellmanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow

instance gronwallBellmanChapterTasteGate : ChapterTasteGate GronwallBellmanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      GronwallBellmanTasteGate_single_carrier_alignment_fromEventFlow
        (GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact GronwallBellmanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance gronwallBellmanFieldFaithful : FieldFaithful GronwallBellmanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := GronwallBellmanTasteGate_single_carrier_alignment_fields
  field_faithful := GronwallBellmanTasteGate_single_carrier_alignment_fields_faithful

instance gronwallBellmanNontrivial : Nontrivial GronwallBellmanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GronwallBellmanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GronwallBellmanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem GronwallBellmanTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GronwallBellmanUp) /\
      (forall x : GronwallBellmanUp,
        exists e : EventFlow, BHistCarrier.fromEventFlow e = some x) /\
      GronwallBellmanTasteGate_single_carrier_alignment_fields
          (GronwallBellmanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨gronwallBellmanChapterTasteGate⟩
  · constructor
    · intro x
      exact
        ⟨GronwallBellmanTasteGate_single_carrier_alignment_toEventFlow x,
          ChapterTasteGate.round_trip x⟩
    · rfl

end BEDC.Derived.GronwallBellmanUp.TasteGate
