import BEDC.Derived.RealOscillationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealOscillationUp : Type where
  | mk (X O C S D W R H T P N : BHist) : RealOscillationUp
  deriving DecidableEq

def realOscillationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realOscillationEncodeBHist h

def realOscillationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realOscillationDecodeBHist tail)

private theorem RealOscillationUpTasteGate_single_carrier_alignment_decode :
    forall h : BHist, realOscillationDecodeBHist (realOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realOscillationFields : RealOscillationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealOscillationUp.mk X O C S D W R H T P N => [X, O, C, S, D, W, R, H, T, P, N]

def realOscillationToEventFlow : RealOscillationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realOscillationEncodeBHist (realOscillationFields x)

private def realOscillationEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realOscillationEventAtDefault index rest

def realOscillationFromEventFlow (ef : EventFlow) : Option RealOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealOscillationUp.mk
      (realOscillationDecodeBHist (realOscillationEventAtDefault 0 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 1 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 2 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 3 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 4 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 5 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 6 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 7 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 8 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 9 ef))
      (realOscillationDecodeBHist (realOscillationEventAtDefault 10 ef)))

private theorem RealOscillationUpTasteGate_single_carrier_alignment_round_trip :
    forall x : RealOscillationUp,
      realOscillationFromEventFlow (realOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X O C S D W R H T P N =>
      change
        some
          (RealOscillationUp.mk
            (realOscillationDecodeBHist (realOscillationEncodeBHist X))
            (realOscillationDecodeBHist (realOscillationEncodeBHist O))
            (realOscillationDecodeBHist (realOscillationEncodeBHist C))
            (realOscillationDecodeBHist (realOscillationEncodeBHist S))
            (realOscillationDecodeBHist (realOscillationEncodeBHist D))
            (realOscillationDecodeBHist (realOscillationEncodeBHist W))
            (realOscillationDecodeBHist (realOscillationEncodeBHist R))
            (realOscillationDecodeBHist (realOscillationEncodeBHist H))
            (realOscillationDecodeBHist (realOscillationEncodeBHist T))
            (realOscillationDecodeBHist (realOscillationEncodeBHist P))
            (realOscillationDecodeBHist (realOscillationEncodeBHist N))) =
          some (RealOscillationUp.mk X O C S D W R H T P N)
      rw [RealOscillationUpTasteGate_single_carrier_alignment_decode X,
        RealOscillationUpTasteGate_single_carrier_alignment_decode O,
        RealOscillationUpTasteGate_single_carrier_alignment_decode C,
        RealOscillationUpTasteGate_single_carrier_alignment_decode S,
        RealOscillationUpTasteGate_single_carrier_alignment_decode D,
        RealOscillationUpTasteGate_single_carrier_alignment_decode W,
        RealOscillationUpTasteGate_single_carrier_alignment_decode R,
        RealOscillationUpTasteGate_single_carrier_alignment_decode H,
        RealOscillationUpTasteGate_single_carrier_alignment_decode T,
        RealOscillationUpTasteGate_single_carrier_alignment_decode P,
        RealOscillationUpTasteGate_single_carrier_alignment_decode N]

private theorem RealOscillationUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealOscillationUp} :
    realOscillationToEventFlow x = realOscillationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realOscillationFromEventFlow (realOscillationToEventFlow x) =
        realOscillationFromEventFlow (realOscillationToEventFlow y) :=
    congrArg realOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealOscillationUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealOscillationUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealOscillationUpTasteGate_single_carrier_alignment_fields :
    forall x y : RealOscillationUp, realOscillationFields x = realOscillationFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 O1 C1 S1 D1 W1 R1 H1 T1 P1 N1 =>
      cases y with
      | mk X2 O2 C2 S2 D2 W2 R2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance realOscillationBHistCarrier : BHistCarrier RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realOscillationToEventFlow
  fromEventFlow := realOscillationFromEventFlow

instance realOscillationChapterTasteGate : ChapterTasteGate RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realOscillationFromEventFlow (realOscillationToEventFlow x) = some x
    exact RealOscillationUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealOscillationUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realOscillationFieldFaithful : FieldFaithful RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realOscillationFields
  field_faithful := RealOscillationUpTasteGate_single_carrier_alignment_fields

instance realOscillationNontrivial : Nontrivial RealOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealOscillationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealOscillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealOscillationUpTasteGate_single_carrier_alignment :
    (forall h : BHist, realOscillationDecodeBHist (realOscillationEncodeBHist h) = h) /\
      (forall x : RealOscillationUp,
        realOscillationFromEventFlow (realOscillationToEventFlow x) = some x) /\
        (forall x y : RealOscillationUp,
          realOscillationToEventFlow x = realOscillationToEventFlow y -> x = y) /\
          realOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealOscillationUpTasteGate_single_carrier_alignment_decode,
      RealOscillationUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RealOscillationUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

theorem RealOscillationTasteGate_single_carrier_alignment :
    (forall h : BHist, realOscillationDecodeBHist (realOscillationEncodeBHist h) = h) /\
      (forall x : RealOscillationUp,
        realOscillationFromEventFlow (realOscillationToEventFlow x) = some x) /\
        (forall x y : RealOscillationUp,
          realOscillationToEventFlow x = realOscillationToEventFlow y -> x = y) /\
          realOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact RealOscillationUpTasteGate_single_carrier_alignment

end BEDC.Derived.RealOscillationUp
