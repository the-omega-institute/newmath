import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitInterchangeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitInterchangeUp : Type where
  | mk
      (continuousFamily uniformLimitRoute sharedModulus regularReadback realSeal
        interchangeTransport transports replay provenance localNameCert : BHist) :
      UniformLimitInterchangeUp
  deriving DecidableEq

def uniformLimitInterchangeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitInterchangeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitInterchangeEncodeBHist h

def uniformLimitInterchangeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitInterchangeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitInterchangeDecodeBHist tail)

private theorem uniformLimitInterchange_decode_encode_bhist :
    ∀ h : BHist, uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitInterchangeFields : UniformLimitInterchangeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitInterchangeUp.mk continuousFamily uniformLimitRoute sharedModulus
      regularReadback realSeal interchangeTransport transports replay provenance localNameCert =>
      [continuousFamily, uniformLimitRoute, sharedModulus, regularReadback, realSeal,
        interchangeTransport, transports, replay, provenance, localNameCert]

def uniformLimitInterchangeToEventFlow : UniformLimitInterchangeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitInterchangeFields x).map uniformLimitInterchangeEncodeBHist

private def uniformLimitInterchangeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformLimitInterchangeEventAtDefault index rest

def uniformLimitInterchangeFromEventFlow : EventFlow → Option UniformLimitInterchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (UniformLimitInterchangeUp.mk
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 0 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 1 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 2 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 3 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 4 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 5 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 6 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 7 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 8 ef))
        (uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEventAtDefault 9 ef)))

private theorem uniformLimitInterchange_round_trip :
    ∀ x : UniformLimitInterchangeUp,
      uniformLimitInterchangeFromEventFlow (uniformLimitInterchangeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk continuousFamily uniformLimitRoute sharedModulus regularReadback realSeal
      interchangeTransport transports replay provenance localNameCert =>
      change
        some
          (UniformLimitInterchangeUp.mk
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist continuousFamily))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist uniformLimitRoute))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist sharedModulus))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist regularReadback))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist realSeal))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist interchangeTransport))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist transports))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist replay))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist provenance))
            (uniformLimitInterchangeDecodeBHist
              (uniformLimitInterchangeEncodeBHist localNameCert))) =
          some
            (UniformLimitInterchangeUp.mk continuousFamily uniformLimitRoute sharedModulus
              regularReadback realSeal interchangeTransport transports replay provenance
              localNameCert)
      rw [uniformLimitInterchange_decode_encode_bhist continuousFamily,
        uniformLimitInterchange_decode_encode_bhist uniformLimitRoute,
        uniformLimitInterchange_decode_encode_bhist sharedModulus,
        uniformLimitInterchange_decode_encode_bhist regularReadback,
        uniformLimitInterchange_decode_encode_bhist realSeal,
        uniformLimitInterchange_decode_encode_bhist interchangeTransport,
        uniformLimitInterchange_decode_encode_bhist transports,
        uniformLimitInterchange_decode_encode_bhist replay,
        uniformLimitInterchange_decode_encode_bhist provenance,
        uniformLimitInterchange_decode_encode_bhist localNameCert]

private theorem uniformLimitInterchangeToEventFlow_injective {x y : UniformLimitInterchangeUp} :
    uniformLimitInterchangeToEventFlow x = uniformLimitInterchangeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitInterchangeFromEventFlow (uniformLimitInterchangeToEventFlow x) =
        uniformLimitInterchangeFromEventFlow (uniformLimitInterchangeToEventFlow y) :=
    congrArg uniformLimitInterchangeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformLimitInterchange_round_trip x).symm
      (Eq.trans hread (uniformLimitInterchange_round_trip y)))

private theorem uniformLimitInterchange_field_faithful :
    ∀ x y : UniformLimitInterchangeUp, uniformLimitInterchangeFields x =
      uniformLimitInterchangeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk continuousFamily₁ uniformLimitRoute₁ sharedModulus₁ regularReadback₁ realSeal₁
      interchangeTransport₁ transports₁ replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk continuousFamily₂ uniformLimitRoute₂ sharedModulus₂ regularReadback₂ realSeal₂
          interchangeTransport₂ transports₂ replay₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance uniformLimitInterchangeBHistCarrier : BHistCarrier UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitInterchangeToEventFlow
  fromEventFlow := uniformLimitInterchangeFromEventFlow

instance uniformLimitInterchangeChapterTasteGate : ChapterTasteGate UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitInterchangeFromEventFlow (uniformLimitInterchangeToEventFlow x) = some x
    exact uniformLimitInterchange_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitInterchangeToEventFlow_injective heq)

instance uniformLimitInterchangeFieldFaithful : FieldFaithful UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitInterchangeFields
  field_faithful := uniformLimitInterchange_field_faithful

instance uniformLimitInterchangeNontrivial : Nontrivial UniformLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitInterchangeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitInterchangeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitInterchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitInterchangeChapterTasteGate

theorem UniformLimitInterchangeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformLimitInterchangeDecodeBHist (uniformLimitInterchangeEncodeBHist h) = h) ∧
      (∀ x : UniformLimitInterchangeUp,
        uniformLimitInterchangeFromEventFlow (uniformLimitInterchangeToEventFlow x) = some x) ∧
        (∀ x y : UniformLimitInterchangeUp,
          uniformLimitInterchangeToEventFlow x = uniformLimitInterchangeToEventFlow y → x = y) ∧
          uniformLimitInterchangeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨uniformLimitInterchange_decode_encode_bhist,
      uniformLimitInterchange_round_trip,
      (fun _ _ heq => uniformLimitInterchangeToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitInterchangeUp
