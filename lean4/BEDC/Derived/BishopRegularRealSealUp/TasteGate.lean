import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularRealSealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularRealSealUp : Type where
  | mk
      (window readback dyadicLedger completionModulus realSeal transport replay provenance
        localName : BHist) :
      BishopRegularRealSealUp
  deriving DecidableEq

def bishopRegularRealSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularRealSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularRealSealEncodeBHist h

def bishopRegularRealSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularRealSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularRealSealDecodeBHist tail)

private theorem bishopRegularRealSeal_decode_encode_bhist :
    ∀ h : BHist,
      bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bishopRegularRealSealToEventFlow : BishopRegularRealSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularRealSealUp.mk window readback dyadicLedger completionModulus realSeal transport
      replay provenance localName =>
      [[BMark.b0],
        bishopRegularRealSealEncodeBHist window,
        [BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist completionModulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bishopRegularRealSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bishopRegularRealSealEncodeBHist localName]

def bishopRegularRealSealFromEventFlow : EventFlow -> Option BishopRegularRealSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadicLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | completionModulus :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (BishopRegularRealSealUp.mk
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    window)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    readback)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    dyadicLedger)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    completionModulus)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    realSeal)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    transport)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    replay)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    provenance)
                                                                                  (bishopRegularRealSealDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem bishopRegularRealSeal_round_trip :
    ∀ x : BishopRegularRealSealUp,
      bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window readback dyadicLedger completionModulus realSeal transport replay provenance
      localName =>
      change
        some
          (BishopRegularRealSealUp.mk
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist window))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist readback))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist dyadicLedger))
            (bishopRegularRealSealDecodeBHist
              (bishopRegularRealSealEncodeBHist completionModulus))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist realSeal))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist transport))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist replay))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist provenance))
            (bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist localName))) =
          some
            (BishopRegularRealSealUp.mk window readback dyadicLedger completionModulus realSeal
              transport replay provenance localName)
      rw [bishopRegularRealSeal_decode_encode_bhist window,
        bishopRegularRealSeal_decode_encode_bhist readback,
        bishopRegularRealSeal_decode_encode_bhist dyadicLedger,
        bishopRegularRealSeal_decode_encode_bhist completionModulus,
        bishopRegularRealSeal_decode_encode_bhist realSeal,
        bishopRegularRealSeal_decode_encode_bhist transport,
        bishopRegularRealSeal_decode_encode_bhist replay,
        bishopRegularRealSeal_decode_encode_bhist provenance,
        bishopRegularRealSeal_decode_encode_bhist localName]

private theorem bishopRegularRealSealToEventFlow_injective
    {x y : BishopRegularRealSealUp} :
    bishopRegularRealSealToEventFlow x = bishopRegularRealSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) =
        bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow y) :=
    congrArg bishopRegularRealSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRegularRealSeal_round_trip x).symm
      (Eq.trans hread (bishopRegularRealSeal_round_trip y)))

instance bishopRegularRealSealBHistCarrier : BHistCarrier BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularRealSealToEventFlow
  fromEventFlow := bishopRegularRealSealFromEventFlow

instance bishopRegularRealSealChapterTasteGate : ChapterTasteGate BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x
    exact bishopRegularRealSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularRealSealToEventFlow_injective heq)

instance bishopRegularRealSealFieldFaithful : FieldFaithful BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | BishopRegularRealSealUp.mk window readback dyadicLedger completionModulus realSeal
        transport replay provenance localName =>
        [window, readback, dyadicLedger, completionModulus, realSeal, transport, replay,
          provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk window readback dyadicLedger completionModulus realSeal transport replay provenance
        localName =>
        cases y with
        | mk window' readback' dyadicLedger' completionModulus' realSeal' transport' replay'
            provenance' localName' =>
            injection hfields with hWindow hTail0
            injection hTail0 with hReadback hTail1
            injection hTail1 with hDyadicLedger hTail2
            injection hTail2 with hCompletionModulus hTail3
            injection hTail3 with hRealSeal hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hReplay hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hLocalName _hNil
            cases hWindow
            cases hReadback
            cases hDyadicLedger
            cases hCompletionModulus
            cases hRealSeal
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

instance bishopRegularRealSealNontrivial : Nontrivial BishopRegularRealSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRegularRealSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRegularRealSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopRegularRealSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRegularRealSealDecodeBHist (bishopRegularRealSealEncodeBHist h) = h) ∧
      (∀ x : BishopRegularRealSealUp,
        bishopRegularRealSealFromEventFlow (bishopRegularRealSealToEventFlow x) = some x) ∧
        (∀ x y : BishopRegularRealSealUp,
          bishopRegularRealSealToEventFlow x =
            bishopRegularRealSealToEventFlow y -> x = y) ∧
          bishopRegularRealSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bishopRegularRealSeal_decode_encode_bhist
  · constructor
    · exact bishopRegularRealSeal_round_trip
    · constructor
      · intro x y heq
        exact bishopRegularRealSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopRegularRealSealUp.TasteGate
