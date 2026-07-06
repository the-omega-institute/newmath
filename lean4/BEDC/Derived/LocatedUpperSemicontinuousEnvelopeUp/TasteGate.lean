import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUpperSemicontinuousEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUpperSemicontinuousEnvelopeUp : Type where
  | mk
      (lower upper located window regular rational real transport replay provenance
        localName : BHist) :
      LocatedUpperSemicontinuousEnvelopeUp
  deriving DecidableEq

def locatedUpperSemicontinuousEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUpperSemicontinuousEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUpperSemicontinuousEnvelopeEncodeBHist h

def locatedUpperSemicontinuousEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUpperSemicontinuousEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUpperSemicontinuousEnvelopeDecodeBHist tail)

private theorem locatedUpperSemicontinuousEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      locatedUpperSemicontinuousEnvelopeDecodeBHist
          (locatedUpperSemicontinuousEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedUpperSemicontinuousEnvelopeFields :
    LocatedUpperSemicontinuousEnvelopeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUpperSemicontinuousEnvelopeUp.mk lower upper located window regular rational real
      transport replay provenance localName =>
      [lower, upper, located, window, regular, rational, real, transport, replay,
        provenance, localName]

def locatedUpperSemicontinuousEnvelopeToEventFlow :
    LocatedUpperSemicontinuousEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedUpperSemicontinuousEnvelopeFields x).map
      locatedUpperSemicontinuousEnvelopeEncodeBHist

def locatedUpperSemicontinuousEnvelopeFromEventFlow :
    EventFlow → Option LocatedUpperSemicontinuousEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | lower :: rest0 =>
      match rest0 with
      | [] => none
      | upper :: rest1 =>
          match rest1 with
          | [] => none
          | located :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | rational :: rest5 =>
                          match rest5 with
                          | [] => none
                          | real :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (LocatedUpperSemicontinuousEnvelopeUp.mk
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        lower)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        upper)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        located)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        window)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        regular)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        rational)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        real)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        transport)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        replay)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        provenance)
                                                      (locatedUpperSemicontinuousEnvelopeDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem locatedUpperSemicontinuousEnvelope_round_trip :
    ∀ x : LocatedUpperSemicontinuousEnvelopeUp,
      locatedUpperSemicontinuousEnvelopeFromEventFlow
          (locatedUpperSemicontinuousEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper located window regular rational real transport replay provenance localName =>
      change
        some
          (LocatedUpperSemicontinuousEnvelopeUp.mk
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist lower))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist upper))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist located))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist window))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist regular))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist rational))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist real))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist transport))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist replay))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist provenance))
            (locatedUpperSemicontinuousEnvelopeDecodeBHist
              (locatedUpperSemicontinuousEnvelopeEncodeBHist localName))) =
          some
            (LocatedUpperSemicontinuousEnvelopeUp.mk lower upper located window regular
              rational real transport replay provenance localName)
      rw [locatedUpperSemicontinuousEnvelope_decode_encode_bhist lower,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist upper,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist located,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist window,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist regular,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist rational,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist real,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist transport,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist replay,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist provenance,
        locatedUpperSemicontinuousEnvelope_decode_encode_bhist localName]

private theorem locatedUpperSemicontinuousEnvelopeToEventFlow_injective
    {x y : LocatedUpperSemicontinuousEnvelopeUp} :
    locatedUpperSemicontinuousEnvelopeToEventFlow x =
        locatedUpperSemicontinuousEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUpperSemicontinuousEnvelopeFromEventFlow
          (locatedUpperSemicontinuousEnvelopeToEventFlow x) =
        locatedUpperSemicontinuousEnvelopeFromEventFlow
          (locatedUpperSemicontinuousEnvelopeToEventFlow y) :=
    congrArg locatedUpperSemicontinuousEnvelopeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedUpperSemicontinuousEnvelope_round_trip x).symm
      (Eq.trans hread (locatedUpperSemicontinuousEnvelope_round_trip y)))

private theorem locatedUpperSemicontinuousEnvelope_fields_faithful :
    ∀ x y : LocatedUpperSemicontinuousEnvelopeUp,
      locatedUpperSemicontinuousEnvelopeFields x =
          locatedUpperSemicontinuousEnvelopeFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lower₁ upper₁ located₁ window₁ regular₁ rational₁ real₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk lower₂ upper₂ located₂ window₂ regular₂ rational₂ real₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance locatedUpperSemicontinuousEnvelopeBHistCarrier :
    BHistCarrier LocatedUpperSemicontinuousEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUpperSemicontinuousEnvelopeToEventFlow
  fromEventFlow := locatedUpperSemicontinuousEnvelopeFromEventFlow

instance locatedUpperSemicontinuousEnvelopeChapterTasteGate :
    ChapterTasteGate LocatedUpperSemicontinuousEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedUpperSemicontinuousEnvelopeFromEventFlow
          (locatedUpperSemicontinuousEnvelopeToEventFlow x) =
        some x
    exact locatedUpperSemicontinuousEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedUpperSemicontinuousEnvelopeToEventFlow_injective heq)

instance locatedUpperSemicontinuousEnvelopeFieldFaithful :
    FieldFaithful LocatedUpperSemicontinuousEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedUpperSemicontinuousEnvelopeFields
  field_faithful := locatedUpperSemicontinuousEnvelope_fields_faithful

instance locatedUpperSemicontinuousEnvelopeNontrivial :
    Nontrivial LocatedUpperSemicontinuousEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedUpperSemicontinuousEnvelopeUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      LocatedUpperSemicontinuousEnvelopeUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedUpperSemicontinuousEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedUpperSemicontinuousEnvelopeChapterTasteGate

theorem LocatedUpperSemicontinuousEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedUpperSemicontinuousEnvelopeDecodeBHist
          (locatedUpperSemicontinuousEnvelopeEncodeBHist h) =
        h) ∧
      (∀ x : LocatedUpperSemicontinuousEnvelopeUp,
        locatedUpperSemicontinuousEnvelopeFromEventFlow
            (locatedUpperSemicontinuousEnvelopeToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedUpperSemicontinuousEnvelopeUp,
          locatedUpperSemicontinuousEnvelopeToEventFlow x =
              locatedUpperSemicontinuousEnvelopeToEventFlow y ->
            x = y) ∧
          locatedUpperSemicontinuousEnvelopeEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact locatedUpperSemicontinuousEnvelope_decode_encode_bhist
  · constructor
    · exact locatedUpperSemicontinuousEnvelope_round_trip
    · constructor
      · intro x y heq
        exact locatedUpperSemicontinuousEnvelopeToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedUpperSemicontinuousEnvelopeUp
