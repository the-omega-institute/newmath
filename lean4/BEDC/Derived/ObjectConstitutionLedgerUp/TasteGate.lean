import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObjectConstitutionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObjectConstitutionLedgerUp : Type where
  | mk :
      (focused identity inscription registry scientific appearance classifier ledger gap transport
        replay provenance name : BHist) → ObjectConstitutionLedgerUp
  deriving DecidableEq

def objectConstitutionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: objectConstitutionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: objectConstitutionLedgerEncodeBHist h

def objectConstitutionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (objectConstitutionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (objectConstitutionLedgerDecodeBHist tail)

private theorem objectConstitutionLedgerDecode_encode_bhist :
    ∀ h : BHist,
      objectConstitutionLedgerDecodeBHist
        (objectConstitutionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def objectConstitutionLedgerToEventFlow :
    ObjectConstitutionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectConstitutionLedgerUp.mk focused identity inscription registry scientific appearance
      classifier ledger gap transport replay provenance name =>
      [[BMark.b0],
        objectConstitutionLedgerEncodeBHist focused,
        [BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist identity,
        [BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist registry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist scientific,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist appearance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        objectConstitutionLedgerEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        objectConstitutionLedgerEncodeBHist name]

private def objectConstitutionLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      objectConstitutionLedgerEventAtDefault index rest

def objectConstitutionLedgerFromEventFlow
    (ef : EventFlow) : Option ObjectConstitutionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ObjectConstitutionLedgerUp.mk
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 1 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 3 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 5 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 7 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 9 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 11 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 13 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 15 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 17 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 19 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 21 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 23 ef))
      (objectConstitutionLedgerDecodeBHist (objectConstitutionLedgerEventAtDefault 25 ef)))

private theorem objectConstitutionLedger_round_trip :
    ∀ x : ObjectConstitutionLedgerUp,
      objectConstitutionLedgerFromEventFlow
        (objectConstitutionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk focused identity inscription registry scientific appearance classifier ledger gap
      transport replay provenance name =>
      change
        some
          (ObjectConstitutionLedgerUp.mk
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist focused))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist identity))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist inscription))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist registry))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist scientific))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist appearance))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist classifier))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist ledger))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist gap))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist transport))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist replay))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist provenance))
            (objectConstitutionLedgerDecodeBHist
              (objectConstitutionLedgerEncodeBHist name))) =
          some
            (ObjectConstitutionLedgerUp.mk focused identity inscription registry scientific
              appearance classifier ledger gap transport replay provenance name)
      rw [objectConstitutionLedgerDecode_encode_bhist focused,
        objectConstitutionLedgerDecode_encode_bhist identity,
        objectConstitutionLedgerDecode_encode_bhist inscription,
        objectConstitutionLedgerDecode_encode_bhist registry,
        objectConstitutionLedgerDecode_encode_bhist scientific,
        objectConstitutionLedgerDecode_encode_bhist appearance,
        objectConstitutionLedgerDecode_encode_bhist classifier,
        objectConstitutionLedgerDecode_encode_bhist ledger,
        objectConstitutionLedgerDecode_encode_bhist gap,
        objectConstitutionLedgerDecode_encode_bhist transport,
        objectConstitutionLedgerDecode_encode_bhist replay,
        objectConstitutionLedgerDecode_encode_bhist provenance,
        objectConstitutionLedgerDecode_encode_bhist name]

private theorem objectConstitutionLedgerToEventFlow_injective
    {x y : ObjectConstitutionLedgerUp} :
    objectConstitutionLedgerToEventFlow x =
      objectConstitutionLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      objectConstitutionLedgerFromEventFlow
          (objectConstitutionLedgerToEventFlow x) =
        objectConstitutionLedgerFromEventFlow
          (objectConstitutionLedgerToEventFlow y) :=
    congrArg objectConstitutionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (objectConstitutionLedger_round_trip x).symm
      (Eq.trans hread (objectConstitutionLedger_round_trip y)))

private def objectConstitutionLedgerFields :
    ObjectConstitutionLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObjectConstitutionLedgerUp.mk focused identity inscription registry scientific appearance
      classifier ledger gap transport replay provenance name =>
      [focused, identity, inscription, registry, scientific, appearance, classifier, ledger, gap,
        transport, replay, provenance, name]

private theorem objectConstitutionLedger_field_faithful :
    ∀ x y : ObjectConstitutionLedgerUp,
      objectConstitutionLedgerFields x = objectConstitutionLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk focused identity inscription registry scientific appearance classifier ledger gap
      transport replay provenance name =>
      cases y with
      | mk focused' identity' inscription' registry' scientific' appearance' classifier'
          ledger' gap' transport' replay' provenance' name' =>
          cases hfields
          rfl

instance objectConstitutionLedgerBHistCarrier :
    BHistCarrier ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := objectConstitutionLedgerToEventFlow
  fromEventFlow := objectConstitutionLedgerFromEventFlow

instance objectConstitutionLedgerChapterTasteGate :
    ChapterTasteGate ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := objectConstitutionLedger_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (objectConstitutionLedgerToEventFlow_injective heq)

instance objectConstitutionLedgerFieldFaithful :
    FieldFaithful ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := objectConstitutionLedgerFields
  field_faithful := objectConstitutionLedger_field_faithful

instance objectConstitutionLedgerNontrivial :
    Nontrivial ObjectConstitutionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObjectConstitutionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ObjectConstitutionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObjectConstitutionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  objectConstitutionLedgerChapterTasteGate

theorem ObjectConstitutionLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        objectConstitutionLedgerDecodeBHist
          (objectConstitutionLedgerEncodeBHist h) = h) ∧
      (∀ x : ObjectConstitutionLedgerUp,
        objectConstitutionLedgerFromEventFlow
          (objectConstitutionLedgerToEventFlow x) = some x) ∧
        (∀ x y : ObjectConstitutionLedgerUp,
          objectConstitutionLedgerToEventFlow x =
            objectConstitutionLedgerToEventFlow y → x = y) ∧
          objectConstitutionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact objectConstitutionLedgerDecode_encode_bhist
  · constructor
    · exact objectConstitutionLedger_round_trip
    · constructor
      · intro x y heq
        exact objectConstitutionLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObjectConstitutionLedgerUp
