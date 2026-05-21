import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlgClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlgClosureUp : Type where
  | mk
      (fieldExtension polynomial rootWitness transport ledger satisfaction localNameCert : BHist) :
        AlgClosureUp
  deriving DecidableEq

def AlgClosureTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def AlgClosureTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: AlgClosureTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: AlgClosureTasteGate_single_carrier_alignment_encodeBHist h

def AlgClosureTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (AlgClosureTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (AlgClosureTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem AlgClosureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      AlgClosureTasteGate_single_carrier_alignment_decodeBHist
          (AlgClosureTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def AlgClosureTasteGate_single_carrier_alignment_fields :
    AlgClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlgClosureUp.mk fieldExtension polynomial rootWitness transport ledger satisfaction
      localNameCert =>
      [fieldExtension, polynomial, rootWitness, transport, ledger, satisfaction, localNameCert]

def AlgClosureTasteGate_single_carrier_alignment_toEventFlow :
    AlgClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AlgClosureUp.mk fieldExtension polynomial rootWitness transport ledger satisfaction
      localNameCert =>
      [AlgClosureTasteGate_single_carrier_alignment_tag,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist fieldExtension,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist polynomial,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist rootWitness,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist transport,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist ledger,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist satisfaction,
        AlgClosureTasteGate_single_carrier_alignment_encodeBHist localNameCert]

private def AlgClosureTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => AlgClosureTasteGate_single_carrier_alignment_eventAt index rest

def AlgClosureTasteGate_single_carrier_alignment_fromEventFlow : EventFlow → Option AlgClosureUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (AlgClosureUp.mk
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 1 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 2 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 3 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 4 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 5 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 6 ef))
          (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
            (AlgClosureTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem AlgClosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AlgClosureUp,
      AlgClosureTasteGate_single_carrier_alignment_fromEventFlow
          (AlgClosureTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fieldExtension polynomial rootWitness transport ledger satisfaction localNameCert =>
      change
        some
          (AlgClosureUp.mk
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist fieldExtension))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist polynomial))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist rootWitness))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist transport))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist ledger))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist satisfaction))
            (AlgClosureTasteGate_single_carrier_alignment_decodeBHist
              (AlgClosureTasteGate_single_carrier_alignment_encodeBHist localNameCert))) =
          some
            (AlgClosureUp.mk fieldExtension polynomial rootWitness transport ledger satisfaction
              localNameCert)
      rw [AlgClosureTasteGate_single_carrier_alignment_decode_encode fieldExtension,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode polynomial,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode rootWitness,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode transport,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode ledger,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode satisfaction,
        AlgClosureTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem AlgClosureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlgClosureUp} :
    AlgClosureTasteGate_single_carrier_alignment_toEventFlow x =
        AlgClosureTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      AlgClosureTasteGate_single_carrier_alignment_fromEventFlow
          (AlgClosureTasteGate_single_carrier_alignment_toEventFlow x) =
        AlgClosureTasteGate_single_carrier_alignment_fromEventFlow
          (AlgClosureTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg AlgClosureTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AlgClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AlgClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem AlgClosureTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AlgClosureUp,
      AlgClosureTasteGate_single_carrier_alignment_fields x =
          AlgClosureTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fieldExtension₁ polynomial₁ rootWitness₁ transport₁ ledger₁ satisfaction₁
      localNameCert₁ =>
      cases y with
      | mk fieldExtension₂ polynomial₂ rootWitness₂ transport₂ ledger₂ satisfaction₂
          localNameCert₂ =>
          cases hfields
          rfl

instance AlgClosureTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier AlgClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := AlgClosureTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := AlgClosureTasteGate_single_carrier_alignment_fromEventFlow

instance AlgClosureTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate AlgClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      AlgClosureTasteGate_single_carrier_alignment_fromEventFlow
          (AlgClosureTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact AlgClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AlgClosureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance AlgClosureTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful AlgClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := AlgClosureTasteGate_single_carrier_alignment_fields
  field_faithful := AlgClosureTasteGate_single_carrier_alignment_fields_faithful

theorem AlgClosureTasteGate_single_carrier_alignment :
    (forall h : BHist,
      AlgClosureTasteGate_single_carrier_alignment_decodeBHist
          (AlgClosureTasteGate_single_carrier_alignment_encodeBHist h) =
        h) /\
      AlgClosureTasteGate_single_carrier_alignment_fields
          (AlgClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] /\
        AlgClosureTasteGate_single_carrier_alignment_toEventFlow
            (AlgClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact AlgClosureTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.AlgClosureUp
