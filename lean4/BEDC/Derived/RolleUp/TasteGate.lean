import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RolleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RolleUp : Type where
  | mk
      (interval endpointEquality continuousMap extremeValue derivativeQuotient interiorWitness
        zeroSeal transport replay provenance name : BHist) :
      RolleUp
  deriving DecidableEq

def RolleUpTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b0]

def RolleUpTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RolleUpTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RolleUpTasteGate_single_carrier_alignment_encodeBHist h

def RolleUpTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (RolleUpTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (RolleUpTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RolleUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RolleUpTasteGate_single_carrier_alignment_decodeBHist
          (RolleUpTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def RolleUpTasteGate_single_carrier_alignment_fields : RolleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RolleUp.mk interval endpointEquality continuousMap extremeValue derivativeQuotient
      interiorWitness zeroSeal transport replay provenance name =>
      [interval, endpointEquality, continuousMap, extremeValue, derivativeQuotient,
        interiorWitness, zeroSeal, transport, replay, provenance, name]

def RolleUpTasteGate_single_carrier_alignment_toEventFlow : RolleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RolleUp.mk interval endpointEquality continuousMap extremeValue derivativeQuotient
      interiorWitness zeroSeal transport replay provenance name =>
      [RolleUpTasteGate_single_carrier_alignment_tag,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist interval,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist endpointEquality,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist continuousMap,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist extremeValue,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist derivativeQuotient,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist interiorWitness,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist zeroSeal,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist transport,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist replay,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist provenance,
        RolleUpTasteGate_single_carrier_alignment_encodeBHist name]

private def RolleUpTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RolleUpTasteGate_single_carrier_alignment_eventAtDefault index rest

def RolleUpTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RolleUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RolleUp.mk
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (RolleUpTasteGate_single_carrier_alignment_decodeBHist
        (RolleUpTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem RolleUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RolleUp,
      RolleUpTasteGate_single_carrier_alignment_fromEventFlow
          (RolleUpTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval endpointEquality continuousMap extremeValue derivativeQuotient interiorWitness
      zeroSeal transport replay provenance name =>
      change
        some
          (RolleUp.mk
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist interval))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist endpointEquality))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist continuousMap))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist extremeValue))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist derivativeQuotient))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist interiorWitness))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist zeroSeal))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist transport))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist replay))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist provenance))
            (RolleUpTasteGate_single_carrier_alignment_decodeBHist
              (RolleUpTasteGate_single_carrier_alignment_encodeBHist name))) =
          some
            (RolleUp.mk interval endpointEquality continuousMap extremeValue
              derivativeQuotient interiorWitness zeroSeal transport replay provenance name)
      rw [RolleUpTasteGate_single_carrier_alignment_decode_encode interval,
        RolleUpTasteGate_single_carrier_alignment_decode_encode endpointEquality,
        RolleUpTasteGate_single_carrier_alignment_decode_encode continuousMap,
        RolleUpTasteGate_single_carrier_alignment_decode_encode extremeValue,
        RolleUpTasteGate_single_carrier_alignment_decode_encode derivativeQuotient,
        RolleUpTasteGate_single_carrier_alignment_decode_encode interiorWitness,
        RolleUpTasteGate_single_carrier_alignment_decode_encode zeroSeal,
        RolleUpTasteGate_single_carrier_alignment_decode_encode transport,
        RolleUpTasteGate_single_carrier_alignment_decode_encode replay,
        RolleUpTasteGate_single_carrier_alignment_decode_encode provenance,
        RolleUpTasteGate_single_carrier_alignment_decode_encode name]

private theorem RolleUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RolleUp} :
    RolleUpTasteGate_single_carrier_alignment_toEventFlow x =
        RolleUpTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RolleUpTasteGate_single_carrier_alignment_fromEventFlow
          (RolleUpTasteGate_single_carrier_alignment_toEventFlow x) =
        RolleUpTasteGate_single_carrier_alignment_fromEventFlow
          (RolleUpTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RolleUpTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RolleUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RolleUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RolleUpTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RolleUp,
      RolleUpTasteGate_single_carrier_alignment_fields x =
          RolleUpTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval1 endpointEquality1 continuousMap1 extremeValue1 derivativeQuotient1
      interiorWitness1 zeroSeal1 transport1 replay1 provenance1 name1 =>
      cases y with
      | mk interval2 endpointEquality2 continuousMap2 extremeValue2 derivativeQuotient2
          interiorWitness2 zeroSeal2 transport2 replay2 provenance2 name2 =>
          cases hfields
          rfl

instance rolleUpBHistCarrier : BHistCarrier RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RolleUpTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RolleUpTasteGate_single_carrier_alignment_fromEventFlow

instance rolleUpChapterTasteGate : ChapterTasteGate RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RolleUpTasteGate_single_carrier_alignment_fromEventFlow
          (RolleUpTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RolleUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RolleUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rolleUpFieldFaithful : FieldFaithful RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RolleUpTasteGate_single_carrier_alignment_fields
  field_faithful := RolleUpTasteGate_single_carrier_alignment_field_faithful

instance rolleUpNontrivial : Nontrivial RolleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RolleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RolleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RolleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rolleUpChapterTasteGate

theorem RolleUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        RolleUpTasteGate_single_carrier_alignment_decodeBHist
            (RolleUpTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
      RolleUpTasteGate_single_carrier_alignment_fields
          (RolleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨RolleUpTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.RolleUp
