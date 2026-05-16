import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EmpiricalRegularityPersistenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EmpiricalRegularityPersistenceUp : Type where
  | mk (measurement regularity classifier errorLedger gap lawConsumer stability failure
      transport replay provenance name : BHist) : EmpiricalRegularityPersistenceUp
  deriving DecidableEq

def empiricalRegularityPersistenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: empiricalRegularityPersistenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: empiricalRegularityPersistenceEncodeBHist h

def empiricalRegularityPersistenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (empiricalRegularityPersistenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (empiricalRegularityPersistenceDecodeBHist tail)

private theorem empiricalRegularityPersistenceDecode_encode_bhist :
    ∀ h : BHist,
      empiricalRegularityPersistenceDecodeBHist
        (empiricalRegularityPersistenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def empiricalRegularityPersistenceEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      empiricalRegularityPersistenceEventAtDefault index rest

def empiricalRegularityPersistenceToEventFlow :
    EmpiricalRegularityPersistenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk measurement regularity classifier errorLedger gap
      lawConsumer stability failure transport replay provenance name =>
      [[BMark.b0],
        empiricalRegularityPersistenceEncodeBHist measurement,
        [BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist regularity,
        [BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist errorLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist lawConsumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        empiricalRegularityPersistenceEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        empiricalRegularityPersistenceEncodeBHist name]

def empiricalRegularityPersistenceFromEventFlow :
    EventFlow → Option EmpiricalRegularityPersistenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (EmpiricalRegularityPersistenceUp.mk
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 1 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 3 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 5 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 7 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 9 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 11 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 13 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 15 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 17 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 19 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 21 flow))
          (empiricalRegularityPersistenceDecodeBHist
            (empiricalRegularityPersistenceEventAtDefault 23 flow)))

private theorem empiricalRegularityPersistence_round_trip :
    ∀ x : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk measurement regularity classifier errorLedger gap lawConsumer stability failure
      transport replay provenance name =>
      change
        some
          (EmpiricalRegularityPersistenceUp.mk
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist measurement))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist regularity))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist classifier))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist errorLedger))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist gap))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist lawConsumer))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist stability))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist failure))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist transport))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist replay))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist provenance))
            (empiricalRegularityPersistenceDecodeBHist
              (empiricalRegularityPersistenceEncodeBHist name))) =
          some
            (EmpiricalRegularityPersistenceUp.mk measurement regularity classifier
              errorLedger gap lawConsumer stability failure transport replay provenance name)
      rw [empiricalRegularityPersistenceDecode_encode_bhist measurement,
        empiricalRegularityPersistenceDecode_encode_bhist regularity,
        empiricalRegularityPersistenceDecode_encode_bhist classifier,
        empiricalRegularityPersistenceDecode_encode_bhist errorLedger,
        empiricalRegularityPersistenceDecode_encode_bhist gap,
        empiricalRegularityPersistenceDecode_encode_bhist lawConsumer,
        empiricalRegularityPersistenceDecode_encode_bhist stability,
        empiricalRegularityPersistenceDecode_encode_bhist failure,
        empiricalRegularityPersistenceDecode_encode_bhist transport,
        empiricalRegularityPersistenceDecode_encode_bhist replay,
        empiricalRegularityPersistenceDecode_encode_bhist provenance,
        empiricalRegularityPersistenceDecode_encode_bhist name]

private theorem empiricalRegularityPersistenceToEventFlow_injective
    {x y : EmpiricalRegularityPersistenceUp} :
    empiricalRegularityPersistenceToEventFlow x =
      empiricalRegularityPersistenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow x) =
        empiricalRegularityPersistenceFromEventFlow
          (empiricalRegularityPersistenceToEventFlow y) :=
    congrArg empiricalRegularityPersistenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (empiricalRegularityPersistence_round_trip x).symm
      (Eq.trans hread (empiricalRegularityPersistence_round_trip y)))

def empiricalRegularityPersistenceFields :
    EmpiricalRegularityPersistenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EmpiricalRegularityPersistenceUp.mk measurement regularity classifier errorLedger gap
      lawConsumer stability failure transport replay provenance name =>
      [measurement, regularity, classifier, errorLedger, gap, lawConsumer, stability, failure,
        transport, replay, provenance, name]

private theorem empiricalRegularityPersistence_fields_faithful :
    ∀ x y : EmpiricalRegularityPersistenceUp,
      empiricalRegularityPersistenceFields x = empiricalRegularityPersistenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk measurement regularity classifier errorLedger gap lawConsumer stability failure
      transport replay provenance name =>
      cases y with
      | mk measurement' regularity' classifier' errorLedger' gap' lawConsumer' stability'
          failure' transport' replay' provenance' name' =>
          cases hfields
          rfl

instance empiricalRegularityPersistenceBHistCarrier :
    BHistCarrier EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := empiricalRegularityPersistenceToEventFlow
  fromEventFlow := empiricalRegularityPersistenceFromEventFlow

instance empiricalRegularityPersistenceChapterTasteGate :
    ChapterTasteGate EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      empiricalRegularityPersistenceFromEventFlow
        (empiricalRegularityPersistenceToEventFlow x) = some x
    exact empiricalRegularityPersistence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (empiricalRegularityPersistenceToEventFlow_injective heq)

instance empiricalRegularityPersistenceFieldFaithful :
    FieldFaithful EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := empiricalRegularityPersistenceFields
  field_faithful := empiricalRegularityPersistence_fields_faithful

instance empiricalRegularityPersistenceNontrivial :
    Nontrivial EmpiricalRegularityPersistenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EmpiricalRegularityPersistenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      EmpiricalRegularityPersistenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EmpiricalRegularityPersistenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  empiricalRegularityPersistenceChapterTasteGate

end BEDC.Derived.EmpiricalRegularityPersistenceUp
