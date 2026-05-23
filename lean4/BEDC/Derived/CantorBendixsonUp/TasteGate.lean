import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorBendixsonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorBendixsonUp : Type where
  | mk
      (closedSet derivativeStage isolatedLedger retainedKernel streamWindows regularReadback
        dyadicLedger realSeal transports replay provenance localNameCert : BHist) :
      CantorBendixsonUp
  deriving DecidableEq

def cantorBendixsonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorBendixsonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorBendixsonEncodeBHist h

def cantorBendixsonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorBendixsonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorBendixsonDecodeBHist tail)

private theorem cantorBendixson_decode_encode_bhist :
    ∀ h : BHist, cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorBendixsonFields : CantorBendixsonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorBendixsonUp.mk closedSet derivativeStage isolatedLedger retainedKernel streamWindows
      regularReadback dyadicLedger realSeal transports replay provenance localNameCert =>
      [closedSet, derivativeStage, isolatedLedger, retainedKernel, streamWindows,
        regularReadback, dyadicLedger, realSeal, transports, replay, provenance,
        localNameCert]

def cantorBendixsonToEventFlow : CantorBendixsonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cantorBendixsonFields x).map cantorBendixsonEncodeBHist

private def cantorBendixsonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorBendixsonEventAtDefault index rest

def cantorBendixsonFromEventFlow : EventFlow → Option CantorBendixsonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorBendixsonUp.mk
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 0 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 1 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 2 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 3 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 4 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 5 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 6 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 7 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 8 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 9 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 10 ef))
        (cantorBendixsonDecodeBHist (cantorBendixsonEventAtDefault 11 ef)))

private theorem cantorBendixson_round_trip :
    ∀ x : CantorBendixsonUp,
      cantorBendixsonFromEventFlow (cantorBendixsonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk closedSet derivativeStage isolatedLedger retainedKernel streamWindows regularReadback
      dyadicLedger realSeal transports replay provenance localNameCert =>
      change
        some
          (CantorBendixsonUp.mk
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist closedSet))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist derivativeStage))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist isolatedLedger))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist retainedKernel))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist streamWindows))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist regularReadback))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist dyadicLedger))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist realSeal))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist transports))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist replay))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist provenance))
            (cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist localNameCert))) =
          some
            (CantorBendixsonUp.mk closedSet derivativeStage isolatedLedger retainedKernel
              streamWindows regularReadback dyadicLedger realSeal transports replay provenance
              localNameCert)
      rw [cantorBendixson_decode_encode_bhist closedSet,
        cantorBendixson_decode_encode_bhist derivativeStage,
        cantorBendixson_decode_encode_bhist isolatedLedger,
        cantorBendixson_decode_encode_bhist retainedKernel,
        cantorBendixson_decode_encode_bhist streamWindows,
        cantorBendixson_decode_encode_bhist regularReadback,
        cantorBendixson_decode_encode_bhist dyadicLedger,
        cantorBendixson_decode_encode_bhist realSeal,
        cantorBendixson_decode_encode_bhist transports,
        cantorBendixson_decode_encode_bhist replay,
        cantorBendixson_decode_encode_bhist provenance,
        cantorBendixson_decode_encode_bhist localNameCert]

theorem cantorBendixsonToEventFlow_injective {x y : CantorBendixsonUp} :
    cantorBendixsonToEventFlow x = cantorBendixsonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorBendixsonFromEventFlow (cantorBendixsonToEventFlow x) =
        cantorBendixsonFromEventFlow (cantorBendixsonToEventFlow y) :=
    congrArg cantorBendixsonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cantorBendixson_round_trip x).symm
      (Eq.trans hread (cantorBendixson_round_trip y)))

private theorem cantorBendixson_field_faithful :
    ∀ x y : CantorBendixsonUp, cantorBendixsonFields x = cantorBendixsonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk closedSet₁ derivativeStage₁ isolatedLedger₁ retainedKernel₁ streamWindows₁
      regularReadback₁ dyadicLedger₁ realSeal₁ transports₁ replay₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk closedSet₂ derivativeStage₂ isolatedLedger₂ retainedKernel₂ streamWindows₂
          regularReadback₂ dyadicLedger₂ realSeal₂ transports₂ replay₂ provenance₂
          localNameCert₂ =>
          cases hfields
          rfl

instance cantorBendixsonBHistCarrier : BHistCarrier CantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorBendixsonToEventFlow
  fromEventFlow := cantorBendixsonFromEventFlow

instance cantorBendixsonChapterTasteGate : ChapterTasteGate CantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorBendixsonFromEventFlow (cantorBendixsonToEventFlow x) = some x
    exact cantorBendixson_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cantorBendixsonToEventFlow_injective heq)

instance cantorBendixsonFieldFaithful : FieldFaithful CantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cantorBendixsonFields
  field_faithful := cantorBendixson_field_faithful

instance cantorBendixsonNontrivial : BEDC.Meta.TasteGate.Nontrivial CantorBendixsonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorBendixsonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorBendixsonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CantorBendixsonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorBendixsonChapterTasteGate

theorem CantorBendixsonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CantorBendixsonUp) ∧
      Nonempty (FieldFaithful CantorBendixsonUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CantorBendixsonUp) ∧
          (∀ h : BHist, cantorBendixsonDecodeBHist (cantorBendixsonEncodeBHist h) = h) ∧
            (∀ x : CantorBendixsonUp,
              cantorBendixsonFromEventFlow (cantorBendixsonToEventFlow x) = some x) ∧
              (∀ x y : CantorBendixsonUp,
                cantorBendixsonToEventFlow x = cantorBendixsonToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cantorBendixsonChapterTasteGate⟩,
      ⟨cantorBendixsonFieldFaithful⟩,
      ⟨cantorBendixsonNontrivial⟩,
      cantorBendixson_decode_encode_bhist,
      cantorBendixson_round_trip,
      (fun _ _ heq => cantorBendixsonToEventFlow_injective heq)⟩

end BEDC.Derived.CantorBendixsonUp
