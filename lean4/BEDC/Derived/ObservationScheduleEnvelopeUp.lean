import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationScheduleEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationScheduleEnvelopeUp : Type where
  | mk :
      (scheduleSource streamSource realWindow refusal handoff transport routes provenance
        nameCert : BHist) →
      ObservationScheduleEnvelopeUp
  deriving DecidableEq

def observationScheduleEnvelopeEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationScheduleEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationScheduleEnvelopeEncodeBHist h

def observationScheduleEnvelopeDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationScheduleEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationScheduleEnvelopeDecodeBHist tail)

private theorem observationScheduleEnvelopeDecode_encode_bhist :
    ∀ h : BHist,
      observationScheduleEnvelopeDecodeBHist
        (observationScheduleEnvelopeEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def observationScheduleEnvelopeToEventFlow :
    ObservationScheduleEnvelopeUp → EventFlow
  | ObservationScheduleEnvelopeUp.mk scheduleSource streamSource realWindow refusal handoff
      transport routes provenance nameCert =>
      [[BMark.b0],
        observationScheduleEnvelopeEncodeBHist scheduleSource,
        [BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist streamSource,
        [BMark.b1, BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist realWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationScheduleEnvelopeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationScheduleEnvelopeEncodeBHist nameCert]

private def observationScheduleEnvelopeRawAt : Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => observationScheduleEnvelopeRawAt n rest

private def observationScheduleEnvelopeLengthEq : Nat → EventFlow → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => observationScheduleEnvelopeLengthEq n rest

def observationScheduleEnvelopeFromEventFlow :
    EventFlow → Option ObservationScheduleEnvelopeUp
  | flow =>
      match observationScheduleEnvelopeLengthEq 18 flow with
      | true =>
          some
            (ObservationScheduleEnvelopeUp.mk
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 1 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 3 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 5 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 7 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 9 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 11 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 13 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 15 flow))
              (observationScheduleEnvelopeDecodeBHist
                (observationScheduleEnvelopeRawAt 17 flow)))
      | false => none

private theorem observationScheduleEnvelope_round_trip :
    ∀ x : ObservationScheduleEnvelopeUp,
      observationScheduleEnvelopeFromEventFlow
          (observationScheduleEnvelopeToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk scheduleSource streamSource realWindow refusal handoff transport routes provenance
      nameCert =>
      change
        some
          (ObservationScheduleEnvelopeUp.mk
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist scheduleSource))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist streamSource))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist realWindow))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist refusal))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist handoff))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist transport))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist routes))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist provenance))
            (observationScheduleEnvelopeDecodeBHist
              (observationScheduleEnvelopeEncodeBHist nameCert))) =
          some
            (ObservationScheduleEnvelopeUp.mk scheduleSource streamSource realWindow refusal
              handoff transport routes provenance nameCert)
      rw [observationScheduleEnvelopeDecode_encode_bhist scheduleSource,
        observationScheduleEnvelopeDecode_encode_bhist streamSource,
        observationScheduleEnvelopeDecode_encode_bhist realWindow,
        observationScheduleEnvelopeDecode_encode_bhist refusal,
        observationScheduleEnvelopeDecode_encode_bhist handoff,
        observationScheduleEnvelopeDecode_encode_bhist transport,
        observationScheduleEnvelopeDecode_encode_bhist routes,
        observationScheduleEnvelopeDecode_encode_bhist provenance,
        observationScheduleEnvelopeDecode_encode_bhist nameCert]

private theorem observationScheduleEnvelopeToEventFlow_injective
    {x y : ObservationScheduleEnvelopeUp} :
    observationScheduleEnvelopeToEventFlow x =
      observationScheduleEnvelopeToEventFlow y → x = y := by
  intro heq
  have hread :
      observationScheduleEnvelopeFromEventFlow
          (observationScheduleEnvelopeToEventFlow x) =
        observationScheduleEnvelopeFromEventFlow
          (observationScheduleEnvelopeToEventFlow y) :=
    congrArg observationScheduleEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationScheduleEnvelope_round_trip x).symm
      (Eq.trans hread (observationScheduleEnvelope_round_trip y)))

instance observationScheduleEnvelopeBHistCarrier :
    BHistCarrier ObservationScheduleEnvelopeUp where
  toEventFlow := observationScheduleEnvelopeToEventFlow
  fromEventFlow := observationScheduleEnvelopeFromEventFlow

instance observationScheduleEnvelopeChapterTasteGate :
    ChapterTasteGate ObservationScheduleEnvelopeUp where
  round_trip := by
    intro x
    change
      observationScheduleEnvelopeFromEventFlow
          (observationScheduleEnvelopeToEventFlow x) =
        some x
    exact observationScheduleEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationScheduleEnvelopeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObservationScheduleEnvelopeUp :=
  observationScheduleEnvelopeChapterTasteGate

instance observationScheduleEnvelopeNontrivial :
    Nontrivial ObservationScheduleEnvelopeUp where
  witness_pair :=
    ⟨ObservationScheduleEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationScheduleEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def observationScheduleEnvelopeFields :
    ObservationScheduleEnvelopeUp → List BHist
  | ObservationScheduleEnvelopeUp.mk scheduleSource streamSource realWindow refusal handoff
      transport routes provenance nameCert =>
      [scheduleSource, streamSource, realWindow, refusal, handoff, transport, routes,
        provenance, nameCert]

private theorem observationScheduleEnvelope_field_faithful_concrete :
    ∀ x y : ObservationScheduleEnvelopeUp,
      observationScheduleEnvelopeFields x =
        observationScheduleEnvelopeFields y → x = y := by
  intro x y hfields
  cases x with
  | mk scheduleSource streamSource realWindow refusal handoff transport routes provenance
      nameCert =>
      cases y with
      | mk scheduleSource' streamSource' realWindow' refusal' handoff' transport' routes'
          provenance' nameCert' =>
          injection hfields with hScheduleSource hTail0
          injection hTail0 with hStreamSource hTail1
          injection hTail1 with hRealWindow hTail2
          injection hTail2 with hRefusal hTail3
          injection hTail3 with hHandoff hTail4
          injection hTail4 with hTransport hTail5
          injection hTail5 with hRoutes hTail6
          injection hTail6 with hProvenance hTail7
          injection hTail7 with hNameCert _hNil
          cases hScheduleSource
          cases hStreamSource
          cases hRealWindow
          cases hRefusal
          cases hHandoff
          cases hTransport
          cases hRoutes
          cases hProvenance
          cases hNameCert
          rfl

instance observationScheduleEnvelopeFieldFaithful :
    FieldFaithful ObservationScheduleEnvelopeUp where
  fields := observationScheduleEnvelopeFields
  field_faithful := observationScheduleEnvelope_field_faithful_concrete

theorem ObservationScheduleEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observationScheduleEnvelopeDecodeBHist
        (observationScheduleEnvelopeEncodeBHist h) = h) ∧
      (∀ x : ObservationScheduleEnvelopeUp,
        observationScheduleEnvelopeFromEventFlow
            (observationScheduleEnvelopeToEventFlow x) =
          some x) ∧
        (∀ x y : ObservationScheduleEnvelopeUp,
          observationScheduleEnvelopeToEventFlow x =
            observationScheduleEnvelopeToEventFlow y → x = y) ∧
          (∀ x y : ObservationScheduleEnvelopeUp,
            observationScheduleEnvelopeFields x =
              observationScheduleEnvelopeFields y → x = y) ∧
            (∃ x y : ObservationScheduleEnvelopeUp, x ≠ y) := by
  constructor
  · exact observationScheduleEnvelopeDecode_encode_bhist
  · constructor
    · exact observationScheduleEnvelope_round_trip
    · constructor
      · intro x y heq
        exact observationScheduleEnvelopeToEventFlow_injective heq
      · constructor
        · exact observationScheduleEnvelope_field_faithful_concrete
        · exact
            ⟨ObservationScheduleEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
              ObservationScheduleEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.ObservationScheduleEnvelopeUp
