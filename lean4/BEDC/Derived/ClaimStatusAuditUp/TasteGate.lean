import BEDC.Derived.ClaimStatusAuditUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClaimStatusAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClaimStatusAuditUp : Type where
  | mk
      (E T R V G S A X H C P N : BHist) : ClaimStatusAuditUp
  deriving DecidableEq

def claimStatusAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: claimStatusAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: claimStatusAuditEncodeBHist h

def claimStatusAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (claimStatusAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (claimStatusAuditDecodeBHist tail)

private theorem claimStatusAudit_decode_encode_bhist :
    ∀ h : BHist, claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def claimStatusAuditToEventFlow : ClaimStatusAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClaimStatusAuditUp.mk E T R V G S A X H C P N =>
      [claimStatusAuditEncodeBHist E,
        claimStatusAuditEncodeBHist T,
        claimStatusAuditEncodeBHist R,
        claimStatusAuditEncodeBHist V,
        claimStatusAuditEncodeBHist G,
        claimStatusAuditEncodeBHist S,
        claimStatusAuditEncodeBHist A,
        claimStatusAuditEncodeBHist X,
        claimStatusAuditEncodeBHist H,
        claimStatusAuditEncodeBHist C,
        claimStatusAuditEncodeBHist P,
        claimStatusAuditEncodeBHist N]

private def claimStatusAuditRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => claimStatusAuditRawAt n rest

private def claimStatusAuditLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => claimStatusAuditLengthEq n rest

def claimStatusAuditFromEventFlow : EventFlow → Option ClaimStatusAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match claimStatusAuditLengthEq 12 flow with
      | true =>
          some
            (ClaimStatusAuditUp.mk
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 0 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 1 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 2 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 3 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 4 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 5 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 6 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 7 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 8 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 9 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 10 flow))
              (claimStatusAuditDecodeBHist (claimStatusAuditRawAt 11 flow)))
      | false => none

private theorem claimStatusAudit_round_trip :
    ∀ x : ClaimStatusAuditUp,
      claimStatusAuditFromEventFlow (claimStatusAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E T R V G S A X H C P N =>
      change
        some
          (ClaimStatusAuditUp.mk
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist E))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist T))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist R))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist V))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist G))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist S))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist A))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist X))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist H))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist C))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist P))
            (claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist N))) =
          some (ClaimStatusAuditUp.mk E T R V G S A X H C P N)
      rw [claimStatusAudit_decode_encode_bhist E,
        claimStatusAudit_decode_encode_bhist T,
        claimStatusAudit_decode_encode_bhist R,
        claimStatusAudit_decode_encode_bhist V,
        claimStatusAudit_decode_encode_bhist G,
        claimStatusAudit_decode_encode_bhist S,
        claimStatusAudit_decode_encode_bhist A,
        claimStatusAudit_decode_encode_bhist X,
        claimStatusAudit_decode_encode_bhist H,
        claimStatusAudit_decode_encode_bhist C,
        claimStatusAudit_decode_encode_bhist P,
        claimStatusAudit_decode_encode_bhist N]

private theorem claimStatusAuditToEventFlow_injective {x y : ClaimStatusAuditUp} :
    claimStatusAuditToEventFlow x = claimStatusAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      claimStatusAuditFromEventFlow (claimStatusAuditToEventFlow x) =
        claimStatusAuditFromEventFlow (claimStatusAuditToEventFlow y) :=
    congrArg claimStatusAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (claimStatusAudit_round_trip x).symm
      (Eq.trans hread (claimStatusAudit_round_trip y)))

instance claimStatusAuditBHistCarrier : BHistCarrier ClaimStatusAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := claimStatusAuditToEventFlow
  fromEventFlow := claimStatusAuditFromEventFlow

instance claimStatusAuditChapterTasteGate : ChapterTasteGate ClaimStatusAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change claimStatusAuditFromEventFlow (claimStatusAuditToEventFlow x) = some x
    exact claimStatusAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (claimStatusAuditToEventFlow_injective heq)

theorem ClaimStatusAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, claimStatusAuditDecodeBHist (claimStatusAuditEncodeBHist h) = h) ∧
      (∀ x : ClaimStatusAuditUp,
        claimStatusAuditFromEventFlow (claimStatusAuditToEventFlow x) = some x) ∧
        (∀ x y : ClaimStatusAuditUp,
          claimStatusAuditToEventFlow x = claimStatusAuditToEventFlow y -> x = y) ∧
          claimStatusAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨claimStatusAudit_decode_encode_bhist,
      claimStatusAudit_round_trip,
      by
        intro x y heq
        exact claimStatusAuditToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ClaimStatusAuditUp
