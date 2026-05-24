import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSequenceAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealSequenceAlgebraUp : Type where
  | mk :
      (sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
        operation outputSeal transport replay provenance localCert : BHist) →
      RealSequenceAlgebraUp
  deriving DecidableEq

def realSequenceAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSequenceAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSequenceAlgebraEncodeBHist h

def realSequenceAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSequenceAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSequenceAlgebraDecodeBHist tail)

theorem RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realSequenceAlgebraFields : RealSequenceAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
      readbackRight dyadicLedger operation outputSeal transport replay provenance localCert =>
      [sourceLeft, sourceRight, windowLeft, windowRight, readbackLeft, readbackRight,
        dyadicLedger, operation, outputSeal, transport, replay, provenance, localCert]

def realSequenceAlgebraToEventFlow : RealSequenceAlgebraUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map realSequenceAlgebraEncodeBHist (realSequenceAlgebraFields x)

private def RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault index rest

def realSequenceAlgebraFromEventFlow : EventFlow → Option RealSequenceAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealSequenceAlgebraUp.mk
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
        (realSequenceAlgebraDecodeBHist
          (RealSequenceAlgebraTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

theorem RealSequenceAlgebraTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealSequenceAlgebraUp,
      realSequenceAlgebraFromEventFlow (realSequenceAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
      operation outputSeal transport replay provenance localCert =>
      change
        some
          (RealSequenceAlgebraUp.mk
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist sourceLeft))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist sourceRight))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist windowLeft))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist windowRight))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist readbackLeft))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist readbackRight))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist dyadicLedger))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist operation))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist outputSeal))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist transport))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist replay))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist provenance))
            (realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist localCert))) =
          some
            (RealSequenceAlgebraUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
              readbackRight dyadicLedger operation outputSeal transport replay provenance localCert)
      rw [RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode sourceLeft,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode sourceRight,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode windowLeft,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode windowRight,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode readbackLeft,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode readbackRight,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode dyadicLedger,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode operation,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode outputSeal,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode transport,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode replay,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode provenance,
        RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode localCert]

theorem RealSequenceAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealSequenceAlgebraUp} :
    realSequenceAlgebraToEventFlow x = realSequenceAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSequenceAlgebraFromEventFlow (realSequenceAlgebraToEventFlow x) =
        realSequenceAlgebraFromEventFlow (realSequenceAlgebraToEventFlow y) :=
    congrArg realSequenceAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealSequenceAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealSequenceAlgebraTasteGate_single_carrier_alignment_round_trip y)))

private theorem realSequenceAlgebra_field_faithful :
    ∀ x y : RealSequenceAlgebraUp, realSequenceAlgebraFields x = realSequenceAlgebraFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk sourceLeft₁ sourceRight₁ windowLeft₁ windowRight₁ readbackLeft₁ readbackRight₁
      dyadicLedger₁ operation₁ outputSeal₁ transport₁ replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk sourceLeft₂ sourceRight₂ windowLeft₂ windowRight₂ readbackLeft₂ readbackRight₂
          dyadicLedger₂ operation₂ outputSeal₂ transport₂ replay₂ provenance₂ localCert₂ =>
          cases h
          rfl

instance realSequenceAlgebraBHistCarrier : BHistCarrier RealSequenceAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSequenceAlgebraToEventFlow
  fromEventFlow := realSequenceAlgebraFromEventFlow

instance realSequenceAlgebraChapterTasteGate : ChapterTasteGate RealSequenceAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSequenceAlgebraFromEventFlow (realSequenceAlgebraToEventFlow x) = some x
    exact RealSequenceAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealSequenceAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realSequenceAlgebraFieldFaithful : FieldFaithful RealSequenceAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSequenceAlgebraFields
  field_faithful := realSequenceAlgebra_field_faithful

instance realSequenceAlgebraNontrivial : Nontrivial RealSequenceAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealSequenceAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealSequenceAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealSequenceAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realSequenceAlgebraChapterTasteGate

theorem RealSequenceAlgebraTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealSequenceAlgebraUp) ∧
      Nonempty (FieldFaithful RealSequenceAlgebraUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealSequenceAlgebraUp) ∧
      (∀ h : BHist, realSequenceAlgebraDecodeBHist (realSequenceAlgebraEncodeBHist h) = h) ∧
      (∀ x : RealSequenceAlgebraUp,
        realSequenceAlgebraFromEventFlow (realSequenceAlgebraToEventFlow x) = some x) ∧
      (∀ x y : RealSequenceAlgebraUp,
        realSequenceAlgebraToEventFlow x = realSequenceAlgebraToEventFlow y → x = y) ∧
      realSequenceAlgebraEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro realSequenceAlgebraChapterTasteGate
  · constructor
    · exact Nonempty.intro realSequenceAlgebraFieldFaithful
    · constructor
      · exact Nonempty.intro realSequenceAlgebraNontrivial
      · constructor
        · exact RealSequenceAlgebraTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact RealSequenceAlgebraTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RealSequenceAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RealSequenceAlgebraUp
