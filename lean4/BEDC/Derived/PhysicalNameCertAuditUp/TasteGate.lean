import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalNameCertAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalNameCertAuditUp : Type where
  | mk (S O M C Y L F H R Q N : BHist) : PhysicalNameCertAuditUp
  deriving DecidableEq

def physicalNameCertAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalNameCertAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalNameCertAuditEncodeBHist h

def physicalNameCertAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalNameCertAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalNameCertAuditDecodeBHist tail)

private theorem physicalNameCertAuditDecode_encode_bhist :
    ∀ h : BHist,
      physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def physicalNameCertAuditFields : PhysicalNameCertAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalNameCertAuditUp.mk S O M C Y L F H R Q N => [S, O, M, C, Y, L, F, H, R, Q, N]

def physicalNameCertAuditToEventFlow : PhysicalNameCertAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalNameCertAuditUp.mk S O M C Y L F H R Q N =>
      [[BMark.b0],
        physicalNameCertAuditEncodeBHist S,
        [BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalNameCertAuditEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalNameCertAuditEncodeBHist N]

private def physicalNameCertAuditRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => physicalNameCertAuditRawAt n rest

private def physicalNameCertAuditLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => physicalNameCertAuditLengthEq n rest

def physicalNameCertAuditFromEventFlow : EventFlow → Option PhysicalNameCertAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match physicalNameCertAuditLengthEq 22 flow with
      | true =>
          some
            (PhysicalNameCertAuditUp.mk
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 1 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 3 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 5 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 7 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 9 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 11 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 13 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 15 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 17 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 19 flow))
              (physicalNameCertAuditDecodeBHist (physicalNameCertAuditRawAt 21 flow)))
      | false => none

private theorem physicalNameCertAudit_round_trip :
    ∀ x : PhysicalNameCertAuditUp,
      physicalNameCertAuditFromEventFlow (physicalNameCertAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S O M C Y L F H R Q N =>
      change
        some
          (PhysicalNameCertAuditUp.mk
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist S))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist O))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist M))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist C))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist Y))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist L))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist F))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist H))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist R))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist Q))
            (physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist N))) =
          some (PhysicalNameCertAuditUp.mk S O M C Y L F H R Q N)
      rw [physicalNameCertAuditDecode_encode_bhist S,
        physicalNameCertAuditDecode_encode_bhist O,
        physicalNameCertAuditDecode_encode_bhist M,
        physicalNameCertAuditDecode_encode_bhist C,
        physicalNameCertAuditDecode_encode_bhist Y,
        physicalNameCertAuditDecode_encode_bhist L,
        physicalNameCertAuditDecode_encode_bhist F,
        physicalNameCertAuditDecode_encode_bhist H,
        physicalNameCertAuditDecode_encode_bhist R,
        physicalNameCertAuditDecode_encode_bhist Q,
        physicalNameCertAuditDecode_encode_bhist N]

private theorem physicalNameCertAuditToEventFlow_injective
    {x y : PhysicalNameCertAuditUp} :
    physicalNameCertAuditToEventFlow x = physicalNameCertAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalNameCertAuditFromEventFlow (physicalNameCertAuditToEventFlow x) =
        physicalNameCertAuditFromEventFlow (physicalNameCertAuditToEventFlow y) :=
    congrArg physicalNameCertAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalNameCertAudit_round_trip x).symm
      (Eq.trans hread (physicalNameCertAudit_round_trip y)))

private theorem physicalNameCertAudit_field_faithful :
    ∀ x y : PhysicalNameCertAuditUp,
      physicalNameCertAuditFields x = physicalNameCertAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 O1 M1 C1 Y1 L1 F1 H1 R1 Q1 N1 =>
      cases y with
      | mk S2 O2 M2 C2 Y2 L2 F2 H2 R2 Q2 N2 =>
          cases hfields
          rfl

instance physicalNameCertAuditBHistCarrier : BHistCarrier PhysicalNameCertAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalNameCertAuditToEventFlow
  fromEventFlow := physicalNameCertAuditFromEventFlow

instance physicalNameCertAuditChapterTasteGate :
    ChapterTasteGate PhysicalNameCertAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalNameCertAuditFromEventFlow (physicalNameCertAuditToEventFlow x) = some x
    exact physicalNameCertAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalNameCertAuditToEventFlow_injective heq)

instance physicalNameCertAuditFieldFaithful : FieldFaithful PhysicalNameCertAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalNameCertAuditFields
  field_faithful := physicalNameCertAudit_field_faithful

instance physicalNameCertAuditNontrivial : Nontrivial PhysicalNameCertAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalNameCertAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhysicalNameCertAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalNameCertAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalNameCertAuditChapterTasteGate

theorem PhysicalNameCertAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalNameCertAuditDecodeBHist (physicalNameCertAuditEncodeBHist h) = h) ∧
      (∀ x : PhysicalNameCertAuditUp,
        physicalNameCertAuditFromEventFlow (physicalNameCertAuditToEventFlow x) = some x) ∧
        (∀ x y : PhysicalNameCertAuditUp,
          physicalNameCertAuditToEventFlow x = physicalNameCertAuditToEventFlow y → x = y) ∧
          physicalNameCertAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨physicalNameCertAuditDecode_encode_bhist,
      physicalNameCertAudit_round_trip,
      (fun _ _ heq => physicalNameCertAuditToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PhysicalNameCertAuditUp
