import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealRootExistenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealRootExistenceUp : Type where
  | mk (I F S B R Q D E H C P N : BHist) : RealRootExistenceUp
  deriving DecidableEq

def realRootExistenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realRootExistenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realRootExistenceEncodeBHist h

def realRootExistenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realRootExistenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realRootExistenceDecodeBHist tail)

private theorem RealRootExistenceTasteGate_decode_encode :
    ∀ h : BHist,
      realRootExistenceDecodeBHist (realRootExistenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realRootExistenceToEventFlow : RealRootExistenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealRootExistenceUp.mk I F S B R Q D E H C P N =>
      [realRootExistenceEncodeBHist I,
        realRootExistenceEncodeBHist F,
        realRootExistenceEncodeBHist S,
        realRootExistenceEncodeBHist B,
        realRootExistenceEncodeBHist R,
        realRootExistenceEncodeBHist Q,
        realRootExistenceEncodeBHist D,
        realRootExistenceEncodeBHist E,
        realRootExistenceEncodeBHist H,
        realRootExistenceEncodeBHist C,
        realRootExistenceEncodeBHist P,
        realRootExistenceEncodeBHist N]

private def realRootExistenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realRootExistenceEventAtDefault index rest

def realRootExistenceFromEventFlow : EventFlow → Option RealRootExistenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealRootExistenceUp.mk
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 0 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 1 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 2 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 3 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 4 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 5 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 6 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 7 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 8 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 9 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 10 ef))
          (realRootExistenceDecodeBHist (realRootExistenceEventAtDefault 11 ef)))

private theorem RealRootExistenceTasteGate_round_trip
    (x : RealRootExistenceUp) :
    realRootExistenceFromEventFlow (realRootExistenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F S B R Q D E H C P N =>
      change
        some
          (RealRootExistenceUp.mk
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist I))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist F))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist S))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist B))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist R))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist Q))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist D))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist E))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist H))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist C))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist P))
            (realRootExistenceDecodeBHist (realRootExistenceEncodeBHist N))) =
          some (RealRootExistenceUp.mk I F S B R Q D E H C P N)
      rw [RealRootExistenceTasteGate_decode_encode I,
        RealRootExistenceTasteGate_decode_encode F,
        RealRootExistenceTasteGate_decode_encode S,
        RealRootExistenceTasteGate_decode_encode B,
        RealRootExistenceTasteGate_decode_encode R,
        RealRootExistenceTasteGate_decode_encode Q,
        RealRootExistenceTasteGate_decode_encode D,
        RealRootExistenceTasteGate_decode_encode E,
        RealRootExistenceTasteGate_decode_encode H,
        RealRootExistenceTasteGate_decode_encode C,
        RealRootExistenceTasteGate_decode_encode P,
        RealRootExistenceTasteGate_decode_encode N]

private theorem RealRootExistenceTasteGate_toEventFlow_injective
    {x y : RealRootExistenceUp} :
    realRootExistenceToEventFlow x = realRootExistenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realRootExistenceFromEventFlow (realRootExistenceToEventFlow x) =
        realRootExistenceFromEventFlow (realRootExistenceToEventFlow y) :=
    congrArg realRootExistenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealRootExistenceTasteGate_round_trip x).symm
      (Eq.trans hread (RealRootExistenceTasteGate_round_trip y)))

instance realRootExistenceBHistCarrier : BHistCarrier RealRootExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realRootExistenceToEventFlow
  fromEventFlow := realRootExistenceFromEventFlow

instance realRootExistenceChapterTasteGate : ChapterTasteGate RealRootExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realRootExistenceFromEventFlow (realRootExistenceToEventFlow x) = some x
    exact RealRootExistenceTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealRootExistenceTasteGate_toEventFlow_injective heq)

instance realRootExistenceFieldFaithful : FieldFaithful RealRootExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun
    | RealRootExistenceUp.mk I F S B R Q D E H C P N => [I, F, S, B, R, Q, D, E, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk I1 F1 S1 B1 R1 Q1 D1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk I2 F2 S2 B2 R2 Q2 D2 E2 H2 C2 P2 N2 =>
            cases hfields
            rfl

instance realRootExistenceNontrivial : Nontrivial RealRootExistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealRootExistenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealRootExistenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealRootExistenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realRootExistenceDecodeBHist (realRootExistenceEncodeBHist h) = h) ∧
      (∀ x : RealRootExistenceUp,
        realRootExistenceFromEventFlow (realRootExistenceToEventFlow x) = some x) ∧
        (∀ x y : RealRootExistenceUp,
          realRootExistenceToEventFlow x = realRootExistenceToEventFlow y → x = y) ∧
          realRootExistenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealRootExistenceTasteGate_decode_encode,
      RealRootExistenceTasteGate_round_trip,
      (fun _ _ heq => RealRootExistenceTasteGate_toEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem RealRootExistenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealRootExistenceUp) ∧
      Nonempty (FieldFaithful RealRootExistenceUp) ∧
      Nonempty (Nontrivial RealRootExistenceUp) ∧
      (∀ h : BHist, realRootExistenceDecodeBHist (realRootExistenceEncodeBHist h) = h) ∧
      (∀ x : RealRootExistenceUp,
        realRootExistenceFromEventFlow (realRootExistenceToEventFlow x) = some x) ∧
      (∀ x y : RealRootExistenceUp,
        realRootExistenceToEventFlow x = realRootExistenceToEventFlow y → x = y) ∧
      realRootExistenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro realRootExistenceChapterTasteGate,
      Nonempty.intro realRootExistenceFieldFaithful,
      Nonempty.intro realRootExistenceNontrivial,
      RealRootExistenceTasteGate_decode_encode,
      RealRootExistenceTasteGate_round_trip,
      (fun _ _ heq => RealRootExistenceTasteGate_toEventFlow_injective heq),
      rfl⟩

end TasteGate

end BEDC.Derived.RealRootExistenceUp
