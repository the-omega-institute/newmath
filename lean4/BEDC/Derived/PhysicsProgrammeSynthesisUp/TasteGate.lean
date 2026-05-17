import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicsProgrammeSynthesisUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicsProgrammeSynthesisUp : Type where
  | mk :
      (route falsification strength verification failure transport replay provenance
        localName : BHist) →
      PhysicsProgrammeSynthesisUp
  deriving DecidableEq

def physicsProgrammeSynthesisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicsProgrammeSynthesisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicsProgrammeSynthesisEncodeBHist h

def physicsProgrammeSynthesisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicsProgrammeSynthesisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicsProgrammeSynthesisDecodeBHist tail)

private theorem physicsProgrammeSynthesis_decode_encode_bhist :
    ∀ h : BHist,
      physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def physicsProgrammeSynthesisToEventFlow :
    PhysicsProgrammeSynthesisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsProgrammeSynthesisUp.mk route falsification strength verification failure transport
      replay provenance localName =>
      [[BMark.b1, BMark.b0, BMark.b1],
        physicsProgrammeSynthesisEncodeBHist route,
        physicsProgrammeSynthesisEncodeBHist falsification,
        physicsProgrammeSynthesisEncodeBHist strength,
        physicsProgrammeSynthesisEncodeBHist verification,
        physicsProgrammeSynthesisEncodeBHist failure,
        physicsProgrammeSynthesisEncodeBHist transport,
        physicsProgrammeSynthesisEncodeBHist replay,
        physicsProgrammeSynthesisEncodeBHist provenance,
        physicsProgrammeSynthesisEncodeBHist localName]

private def physicsProgrammeSynthesisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => physicsProgrammeSynthesisEventAtDefault index rest

def physicsProgrammeSynthesisFromEventFlow :
    EventFlow → Option PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (PhysicsProgrammeSynthesisUp.mk
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 1 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 2 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 3 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 4 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 5 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 6 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 7 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 8 ef))
        (physicsProgrammeSynthesisDecodeBHist (physicsProgrammeSynthesisEventAtDefault 9 ef)))

def physicsProgrammeSynthesisFields : PhysicsProgrammeSynthesisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicsProgrammeSynthesisUp.mk route falsification strength verification failure transport
      replay provenance localName =>
      [route, falsification, strength, verification, failure, transport, replay, provenance,
        localName]

private theorem physicsProgrammeSynthesis_round_trip :
    ∀ x : PhysicsProgrammeSynthesisUp,
      physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow x) = some x :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk route falsification strength verification failure transport replay provenance localName =>
      change
        some
          (PhysicsProgrammeSynthesisUp.mk
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist route))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist falsification))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist strength))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist verification))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist failure))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist transport))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist replay))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist provenance))
            (physicsProgrammeSynthesisDecodeBHist
              (physicsProgrammeSynthesisEncodeBHist localName))) =
          some
            (PhysicsProgrammeSynthesisUp.mk route falsification strength verification failure
              transport replay provenance localName)
      rw [physicsProgrammeSynthesis_decode_encode_bhist route,
        physicsProgrammeSynthesis_decode_encode_bhist falsification,
        physicsProgrammeSynthesis_decode_encode_bhist strength,
        physicsProgrammeSynthesis_decode_encode_bhist verification,
        physicsProgrammeSynthesis_decode_encode_bhist failure,
        physicsProgrammeSynthesis_decode_encode_bhist transport,
        physicsProgrammeSynthesis_decode_encode_bhist replay,
        physicsProgrammeSynthesis_decode_encode_bhist provenance,
        physicsProgrammeSynthesis_decode_encode_bhist localName]

private theorem physicsProgrammeSynthesisToEventFlow_injective
    {x y : PhysicsProgrammeSynthesisUp} :
    physicsProgrammeSynthesisToEventFlow x = physicsProgrammeSynthesisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow x) =
        physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow y) :=
    congrArg physicsProgrammeSynthesisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicsProgrammeSynthesis_round_trip x).symm
      (Eq.trans hread (physicsProgrammeSynthesis_round_trip y)))

private theorem physicsProgrammeSynthesis_field_faithful :
    ∀ x y : PhysicsProgrammeSynthesisUp,
      physicsProgrammeSynthesisFields x = physicsProgrammeSynthesisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk route₁ falsification₁ strength₁ verification₁ failure₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk route₂ falsification₂ strength₂ verification₂ failure₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection h with hRoute t1
          injection t1 with hFalsification t2
          injection t2 with hStrength t3
          injection t3 with hVerification t4
          injection t4 with hFailure t5
          injection t5 with hTransport t6
          injection t6 with hReplay t7
          injection t7 with hProvenance t8
          injection t8 with hLocalName _
          cases hRoute
          cases hFalsification
          cases hStrength
          cases hVerification
          cases hFailure
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hLocalName
          rfl

instance physicsProgrammeSynthesisBHistCarrier :
    BHistCarrier PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicsProgrammeSynthesisToEventFlow
  fromEventFlow := physicsProgrammeSynthesisFromEventFlow

instance physicsProgrammeSynthesisChapterTasteGate :
    ChapterTasteGate PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicsProgrammeSynthesisFromEventFlow (physicsProgrammeSynthesisToEventFlow x) =
      some x
    exact physicsProgrammeSynthesis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicsProgrammeSynthesisToEventFlow_injective heq)

instance physicsProgrammeSynthesisFieldFaithful :
    FieldFaithful PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicsProgrammeSynthesisFields
  field_faithful := physicsProgrammeSynthesis_field_faithful

instance physicsProgrammeSynthesisNontrivial :
    Nontrivial PhysicsProgrammeSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicsProgrammeSynthesisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicsProgrammeSynthesisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicsProgrammeSynthesisChapterTasteGate

def taste_gate_witness : FieldFaithful PhysicsProgrammeSynthesisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicsProgrammeSynthesisFieldFaithful

end BEDC.Derived.PhysicsProgrammeSynthesisUp.TasteGate
