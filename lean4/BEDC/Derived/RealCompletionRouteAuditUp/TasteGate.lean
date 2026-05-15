import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionRouteAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionRouteAuditUp : Type where
  | mk :
      (completionRoute limitSeal streamWindow readback dyadicTolerance transport
        continuation provenance name verdict : BHist) →
      RealCompletionRouteAuditUp
  deriving DecidableEq

def realCompletionRouteAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionRouteAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionRouteAuditEncodeBHist h

def realCompletionRouteAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionRouteAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionRouteAuditDecodeBHist tail)

private theorem realCompletionRouteAuditDecode_encode_bhist :
    ∀ h : BHist,
      realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionRouteAuditFields : RealCompletionRouteAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionRouteAuditUp.mk completionRoute limitSeal streamWindow readback
      dyadicTolerance transport continuation provenance name verdict =>
      [completionRoute, limitSeal, streamWindow, readback, dyadicTolerance, transport,
        continuation, provenance, name, verdict]

def realCompletionRouteAuditToEventFlow : RealCompletionRouteAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionRouteAuditUp.mk completionRoute limitSeal streamWindow readback
      dyadicTolerance transport continuation provenance name verdict =>
      [[BMark.b0],
        realCompletionRouteAuditEncodeBHist completionRoute,
        [BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletionRouteAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realCompletionRouteAuditEncodeBHist verdict]

private def realCompletionRouteAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCompletionRouteAuditEventAtDefault index rest

def realCompletionRouteAuditFromEventFlow :
    EventFlow → Option RealCompletionRouteAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealCompletionRouteAuditUp.mk
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 1 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 3 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 5 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 7 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 9 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 11 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 13 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 15 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 17 ef))
        (realCompletionRouteAuditDecodeBHist (realCompletionRouteAuditEventAtDefault 19 ef)))

private theorem realCompletionRouteAudit_round_trip :
    ∀ x : RealCompletionRouteAuditUp,
      realCompletionRouteAuditFromEventFlow (realCompletionRouteAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk completionRoute limitSeal streamWindow readback dyadicTolerance transport continuation
      provenance name verdict =>
      change
        some
            (RealCompletionRouteAuditUp.mk
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist completionRoute))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist limitSeal))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist streamWindow))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist readback))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist dyadicTolerance))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist transport))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist continuation))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist provenance))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist name))
              (realCompletionRouteAuditDecodeBHist
                (realCompletionRouteAuditEncodeBHist verdict))) =
          some
            (RealCompletionRouteAuditUp.mk completionRoute limitSeal streamWindow readback
              dyadicTolerance transport continuation provenance name verdict)
      rw [realCompletionRouteAuditDecode_encode_bhist completionRoute,
        realCompletionRouteAuditDecode_encode_bhist limitSeal,
        realCompletionRouteAuditDecode_encode_bhist streamWindow,
        realCompletionRouteAuditDecode_encode_bhist readback,
        realCompletionRouteAuditDecode_encode_bhist dyadicTolerance,
        realCompletionRouteAuditDecode_encode_bhist transport,
        realCompletionRouteAuditDecode_encode_bhist continuation,
        realCompletionRouteAuditDecode_encode_bhist provenance,
        realCompletionRouteAuditDecode_encode_bhist name,
        realCompletionRouteAuditDecode_encode_bhist verdict]

private theorem realCompletionRouteAuditToEventFlow_injective
    {x y : RealCompletionRouteAuditUp} :
    realCompletionRouteAuditToEventFlow x = realCompletionRouteAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionRouteAuditFromEventFlow (realCompletionRouteAuditToEventFlow x) =
        realCompletionRouteAuditFromEventFlow (realCompletionRouteAuditToEventFlow y) :=
    congrArg realCompletionRouteAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionRouteAudit_round_trip x).symm
      (Eq.trans hread (realCompletionRouteAudit_round_trip y)))

private theorem realCompletionRouteAudit_field_faithful :
    ∀ x y : RealCompletionRouteAuditUp,
      realCompletionRouteAuditFields x = realCompletionRouteAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk completionRoute₁ limitSeal₁ streamWindow₁ readback₁ dyadicTolerance₁ transport₁
      continuation₁ provenance₁ name₁ verdict₁ =>
      cases y with
      | mk completionRoute₂ limitSeal₂ streamWindow₂ readback₂ dyadicTolerance₂ transport₂
          continuation₂ provenance₂ name₂ verdict₂ =>
          cases h
          rfl

instance realCompletionRouteAuditBHistCarrier :
    BHistCarrier RealCompletionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionRouteAuditToEventFlow
  fromEventFlow := realCompletionRouteAuditFromEventFlow

instance realCompletionRouteAuditChapterTasteGate :
    ChapterTasteGate RealCompletionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCompletionRouteAuditFromEventFlow
        (realCompletionRouteAuditToEventFlow x) = some x
    exact realCompletionRouteAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionRouteAuditToEventFlow_injective heq)

instance realCompletionRouteAuditFieldFaithful :
    FieldFaithful RealCompletionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionRouteAuditFields
  field_faithful := realCompletionRouteAudit_field_faithful

instance realCompletionRouteAuditNontrivial :
    Nontrivial RealCompletionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionRouteAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletionRouteAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletionRouteAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionRouteAuditChapterTasteGate

theorem RealCompletionRouteAuditTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealCompletionRouteAuditUp) ∧
      Nonempty (ChapterTasteGate RealCompletionRouteAuditUp) ∧
      Nonempty (FieldFaithful RealCompletionRouteAuditUp) ∧
      Nonempty (Nontrivial RealCompletionRouteAuditUp) ∧
      realCompletionRouteAuditEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      realCompletionRouteAuditEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨realCompletionRouteAuditBHistCarrier⟩,
      ⟨realCompletionRouteAuditChapterTasteGate⟩,
      ⟨realCompletionRouteAuditFieldFaithful⟩,
      ⟨realCompletionRouteAuditNontrivial⟩,
      rfl,
      rfl⟩

end BEDC.Derived.RealCompletionRouteAuditUp
