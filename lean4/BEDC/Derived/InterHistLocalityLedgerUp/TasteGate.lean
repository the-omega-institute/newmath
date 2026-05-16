import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterHistLocalityLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistLocalityLedgerUp : Type where
  | mk :
      (sourceLeft sourceRight transport continuation localityCell invariant provenance
        localName : BHist) →
      InterHistLocalityLedgerUp
  deriving DecidableEq

def interHistLocalityLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistLocalityLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistLocalityLedgerEncodeBHist h

def interHistLocalityLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistLocalityLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistLocalityLedgerDecodeBHist tail)

private theorem interHistLocalityLedger_decode_encode_bhist :
    ∀ h : BHist,
      interHistLocalityLedgerDecodeBHist
        (interHistLocalityLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def interHistLocalityLedgerToEventFlow :
    InterHistLocalityLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation localityCell
      invariant provenance localName =>
      [[BMark.b0],
        interHistLocalityLedgerEncodeBHist sourceLeft,
        [BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist sourceRight,
        [BMark.b1, BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist localityCell,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistLocalityLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        interHistLocalityLedgerEncodeBHist localName]

def interHistLocalityLedgerFromEventFlow :
    EventFlow → Option InterHistLocalityLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localityCell :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | invariant :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | localName ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] =>
                                                                      some
                                                                        (InterHistLocalityLedgerUp.mk
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            sourceLeft)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            sourceRight)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            transport)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            continuation)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            localityCell)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            invariant)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            provenance)
                                                                          (interHistLocalityLedgerDecodeBHist
                                                                            localName))
                                                                  | _ :: _ =>
                                                                      none

private theorem interHistLocalityLedger_round_trip :
    ∀ x : InterHistLocalityLedgerUp,
      interHistLocalityLedgerFromEventFlow
        (interHistLocalityLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight transport continuation localityCell invariant provenance
      localName =>
      change
        some
          (InterHistLocalityLedgerUp.mk
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist sourceLeft))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist sourceRight))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist transport))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist continuation))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist localityCell))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist invariant))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist provenance))
            (interHistLocalityLedgerDecodeBHist
              (interHistLocalityLedgerEncodeBHist localName))) =
          some
            (InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation
              localityCell invariant provenance localName)
      rw [interHistLocalityLedger_decode_encode_bhist sourceLeft,
        interHistLocalityLedger_decode_encode_bhist sourceRight,
        interHistLocalityLedger_decode_encode_bhist transport,
        interHistLocalityLedger_decode_encode_bhist continuation,
        interHistLocalityLedger_decode_encode_bhist localityCell,
        interHistLocalityLedger_decode_encode_bhist invariant,
        interHistLocalityLedger_decode_encode_bhist provenance,
        interHistLocalityLedger_decode_encode_bhist localName]

private theorem interHistLocalityLedgerToEventFlow_injective
    {x y : InterHistLocalityLedgerUp} :
    interHistLocalityLedgerToEventFlow x =
      interHistLocalityLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistLocalityLedgerFromEventFlow
          (interHistLocalityLedgerToEventFlow x) =
        interHistLocalityLedgerFromEventFlow
          (interHistLocalityLedgerToEventFlow y) :=
    congrArg interHistLocalityLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistLocalityLedger_round_trip x).symm
      (Eq.trans hread (interHistLocalityLedger_round_trip y)))

instance interHistLocalityLedgerBHistCarrier :
    BHistCarrier InterHistLocalityLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistLocalityLedgerToEventFlow
  fromEventFlow := interHistLocalityLedgerFromEventFlow

instance interHistLocalityLedgerChapterTasteGate :
    ChapterTasteGate InterHistLocalityLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      interHistLocalityLedgerFromEventFlow
        (interHistLocalityLedgerToEventFlow x) = some x
    exact interHistLocalityLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistLocalityLedgerToEventFlow_injective heq)

instance interHistLocalityLedgerFieldFaithful :
    FieldFaithful InterHistLocalityLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation localityCell
        invariant provenance localName =>
        [sourceLeft, sourceRight, transport, continuation, localityCell, invariant,
          provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk sourceLeft sourceRight transport continuation localityCell invariant provenance
        localName =>
        cases y with
        | mk sourceLeft' sourceRight' transport' continuation' localityCell' invariant'
            provenance' localName' =>
            injection hfields with hSourceLeft hTail0
            injection hTail0 with hSourceRight hTail1
            injection hTail1 with hTransport hTail2
            injection hTail2 with hContinuation hTail3
            injection hTail3 with hLocalityCell hTail4
            injection hTail4 with hInvariant hTail5
            injection hTail5 with hProvenance hTail6
            injection hTail6 with hLocalName _hNil
            cases hSourceLeft
            cases hSourceRight
            cases hTransport
            cases hContinuation
            cases hLocalityCell
            cases hInvariant
            cases hProvenance
            cases hLocalName
            rfl

def taste_gate : ChapterTasteGate InterHistLocalityLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  interHistLocalityLedgerChapterTasteGate

theorem InterHistLocalityLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      interHistLocalityLedgerDecodeBHist
        (interHistLocalityLedgerEncodeBHist h) = h) ∧
      (∀ x : InterHistLocalityLedgerUp,
        interHistLocalityLedgerFromEventFlow
          (interHistLocalityLedgerToEventFlow x) = some x) ∧
        (∀ x y : InterHistLocalityLedgerUp,
          interHistLocalityLedgerToEventFlow x =
            interHistLocalityLedgerToEventFlow y → x = y) ∧
          interHistLocalityLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact interHistLocalityLedger_decode_encode_bhist
  · constructor
    · exact interHistLocalityLedger_round_trip
    · constructor
      · intro x y heq
        exact interHistLocalityLedgerToEventFlow_injective heq
      · rfl

theorem InterHistLocalityLedger_symmetric_route_source_swap_separates :
    FieldFaithful.fields
        (InterHistLocalityLedgerUp.mk (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty)
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) ≠
      FieldFaithful.fields
        (InterHistLocalityLedgerUp.mk (BHist.e1 BHist.Empty) (BHist.e0 BHist.Empty)
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  change
    [BHist.e0 BHist.Empty, BHist.e1 BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] =
      [BHist.e1 BHist.Empty, BHist.e0 BHist.Empty, BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] at h
  injection h with hSourceLeft _hTail
  cases hSourceLeft

theorem InterHistLocalityLedgerLocalityCell_handoff_separation
    {sourceLeft sourceRight transport continuation localityCell provenance localName : BHist} :
    localityCell ≠ BHist.Empty →
      BHistCarrier.toEventFlow
          (InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation localityCell
            BHist.Empty provenance localName) ≠
        BHistCarrier.toEventFlow
          (InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation BHist.Empty
            BHist.Empty provenance localName) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hlocalityCell heq
  apply hlocalityCell
  have hcarrier :
      InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation localityCell
          BHist.Empty provenance localName =
        InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation BHist.Empty
          BHist.Empty provenance localName := by
    apply interHistLocalityLedgerToEventFlow_injective
    change
      interHistLocalityLedgerToEventFlow
          (InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation localityCell
            BHist.Empty provenance localName) =
        interHistLocalityLedgerToEventFlow
          (InterHistLocalityLedgerUp.mk sourceLeft sourceRight transport continuation BHist.Empty
            BHist.Empty provenance localName)
    exact heq
  cases hcarrier
  rfl

end BEDC.Derived.InterHistLocalityLedgerUp
