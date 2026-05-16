import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorClosureClassifierAuditUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorClosureClassifierAuditUp : Type where
  | mk :
      (signature generator branch classifier audit transport replay provenance nameCert : BHist) →
        RecursorClosureClassifierAuditUp
  deriving DecidableEq

def recursorClosureClassifierAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorClosureClassifierAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorClosureClassifierAuditEncodeBHist h

def recursorClosureClassifierAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorClosureClassifierAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorClosureClassifierAuditDecodeBHist tail)

private theorem recursorClosureClassifierAudit_decode_encode_bhist :
    ∀ h : BHist,
      recursorClosureClassifierAuditDecodeBHist
        (recursorClosureClassifierAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def recursorClosureClassifierAuditToEventFlow :
    RecursorClosureClassifierAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorClosureClassifierAuditUp.mk signature generator branch classifier audit transport
      replay provenance nameCert =>
      [[BMark.b0],
        recursorClosureClassifierAuditEncodeBHist signature,
        [BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist generator,
        [BMark.b1, BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist branch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        recursorClosureClassifierAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        recursorClosureClassifierAuditEncodeBHist nameCert]

private def recursorClosureClassifierAuditRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => recursorClosureClassifierAuditRawAt n rest

private def recursorClosureClassifierAuditLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => recursorClosureClassifierAuditLengthEq n rest

def recursorClosureClassifierAuditFromEventFlow :
    EventFlow → Option RecursorClosureClassifierAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match recursorClosureClassifierAuditLengthEq 18 flow with
      | true =>
          some
            (RecursorClosureClassifierAuditUp.mk
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 1 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 3 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 5 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 7 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 9 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 11 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 13 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 15 flow))
              (recursorClosureClassifierAuditDecodeBHist
                (recursorClosureClassifierAuditRawAt 17 flow)))
      | false => none

private theorem recursorClosureClassifierAudit_round_trip :
    ∀ x : RecursorClosureClassifierAuditUp,
      recursorClosureClassifierAuditFromEventFlow
        (recursorClosureClassifierAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature generator branch classifier audit transport replay provenance nameCert =>
      change
        some
          (RecursorClosureClassifierAuditUp.mk
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist signature))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist generator))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist branch))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist classifier))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist audit))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist transport))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist replay))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist provenance))
            (recursorClosureClassifierAuditDecodeBHist
              (recursorClosureClassifierAuditEncodeBHist nameCert))) =
          some
            (RecursorClosureClassifierAuditUp.mk signature generator branch classifier audit
              transport replay provenance nameCert)
      rw [recursorClosureClassifierAudit_decode_encode_bhist signature,
        recursorClosureClassifierAudit_decode_encode_bhist generator,
        recursorClosureClassifierAudit_decode_encode_bhist branch,
        recursorClosureClassifierAudit_decode_encode_bhist classifier,
        recursorClosureClassifierAudit_decode_encode_bhist audit,
        recursorClosureClassifierAudit_decode_encode_bhist transport,
        recursorClosureClassifierAudit_decode_encode_bhist replay,
        recursorClosureClassifierAudit_decode_encode_bhist provenance,
        recursorClosureClassifierAudit_decode_encode_bhist nameCert]

private theorem recursorClosureClassifierAuditToEventFlow_injective
    {x y : RecursorClosureClassifierAuditUp} :
    recursorClosureClassifierAuditToEventFlow x =
      recursorClosureClassifierAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorClosureClassifierAuditFromEventFlow
          (recursorClosureClassifierAuditToEventFlow x) =
        recursorClosureClassifierAuditFromEventFlow
          (recursorClosureClassifierAuditToEventFlow y) :=
    congrArg recursorClosureClassifierAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorClosureClassifierAudit_round_trip x).symm
      (Eq.trans hread (recursorClosureClassifierAudit_round_trip y)))

instance recursorClosureClassifierAuditBHistCarrier :
    BHistCarrier RecursorClosureClassifierAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorClosureClassifierAuditToEventFlow
  fromEventFlow := recursorClosureClassifierAuditFromEventFlow

instance recursorClosureClassifierAuditChapterTasteGate :
    ChapterTasteGate RecursorClosureClassifierAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      recursorClosureClassifierAuditFromEventFlow
        (recursorClosureClassifierAuditToEventFlow x) = some x
    exact recursorClosureClassifierAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorClosureClassifierAuditToEventFlow_injective heq)

instance recursorClosureClassifierAuditFieldFaithful :
    FieldFaithful RecursorClosureClassifierAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RecursorClosureClassifierAuditUp.mk signature generator branch classifier audit
        transport replay provenance nameCert =>
        [signature, generator, branch, classifier, audit, transport, replay, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk signature1 generator1 branch1 classifier1 audit1 transport1 replay1 provenance1
        nameCert1 =>
        cases y with
        | mk signature2 generator2 branch2 classifier2 audit2 transport2 replay2 provenance2
            nameCert2 =>
            cases h
            rfl

instance recursorClosureClassifierAuditNontrivial :
    Nontrivial RecursorClosureClassifierAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorClosureClassifierAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorClosureClassifierAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RecursorClosureClassifierAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorClosureClassifierAuditChapterTasteGate

theorem RecursorClosureClassifierAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      recursorClosureClassifierAuditDecodeBHist
        (recursorClosureClassifierAuditEncodeBHist h) = h) ∧
      (∀ x : RecursorClosureClassifierAuditUp,
        recursorClosureClassifierAuditFromEventFlow
          (recursorClosureClassifierAuditToEventFlow x) = some x) ∧
        (∀ x y : RecursorClosureClassifierAuditUp,
          recursorClosureClassifierAuditToEventFlow x =
            recursorClosureClassifierAuditToEventFlow y → x = y) ∧
          recursorClosureClassifierAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨recursorClosureClassifierAudit_decode_encode_bhist,
      recursorClosureClassifierAudit_round_trip,
      by
        intro x y heq
        exact recursorClosureClassifierAuditToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RecursorClosureClassifierAuditUp.TasteGate
