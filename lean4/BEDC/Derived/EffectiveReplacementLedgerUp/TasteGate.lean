import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveReplacementLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveReplacementLedgerUp : Type where
  | mk :
      (choiceWitness quotientTransport propextTransport axiomPurity transport continuation
        provenance name : BHist) ->
      EffectiveReplacementLedgerUp
  deriving DecidableEq

def effectiveReplacementLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveReplacementLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveReplacementLedgerEncodeBHist h

def effectiveReplacementLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveReplacementLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveReplacementLedgerDecodeBHist tail)

private theorem effectiveReplacementLedgerDecode_encode_bhist :
    forall h : BHist,
      effectiveReplacementLedgerDecodeBHist (effectiveReplacementLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def effectiveReplacementLedgerToEventFlow : EffectiveReplacementLedgerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport axiomPurity
      transport continuation provenance name =>
      [[BMark.b0],
        effectiveReplacementLedgerEncodeBHist choiceWitness,
        [BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist quotientTransport,
        [BMark.b1, BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist propextTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist axiomPurity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveReplacementLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        effectiveReplacementLedgerEncodeBHist name]

def effectiveReplacementLedgerFromEventFlow : EventFlow -> Option EffectiveReplacementLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | choiceWitness :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | quotientTransport :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | propextTransport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | axiomPurity :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (EffectiveReplacementLedgerUp.mk
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            choiceWitness)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            quotientTransport)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            propextTransport)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            axiomPurity)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            transport)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            continuation)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            provenance)
                                                                          (effectiveReplacementLedgerDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem effectiveReplacementLedger_round_trip :
    forall x : EffectiveReplacementLedgerUp,
      effectiveReplacementLedgerFromEventFlow (effectiveReplacementLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk choiceWitness quotientTransport propextTransport axiomPurity transport continuation
      provenance name =>
      change
        some
          (EffectiveReplacementLedgerUp.mk
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist choiceWitness))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist quotientTransport))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist propextTransport))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist axiomPurity))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist transport))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist continuation))
            (effectiveReplacementLedgerDecodeBHist
              (effectiveReplacementLedgerEncodeBHist provenance))
            (effectiveReplacementLedgerDecodeBHist (effectiveReplacementLedgerEncodeBHist name))) =
          some
            (EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport
              axiomPurity transport continuation provenance name)
      rw [effectiveReplacementLedgerDecode_encode_bhist choiceWitness,
        effectiveReplacementLedgerDecode_encode_bhist quotientTransport,
        effectiveReplacementLedgerDecode_encode_bhist propextTransport,
        effectiveReplacementLedgerDecode_encode_bhist axiomPurity,
        effectiveReplacementLedgerDecode_encode_bhist transport,
        effectiveReplacementLedgerDecode_encode_bhist continuation,
        effectiveReplacementLedgerDecode_encode_bhist provenance,
        effectiveReplacementLedgerDecode_encode_bhist name]

private theorem effectiveReplacementLedgerToEventFlow_injective
    {x y : EffectiveReplacementLedgerUp} :
    effectiveReplacementLedgerToEventFlow x = effectiveReplacementLedgerToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveReplacementLedgerFromEventFlow (effectiveReplacementLedgerToEventFlow x) =
        effectiveReplacementLedgerFromEventFlow (effectiveReplacementLedgerToEventFlow y) :=
    congrArg effectiveReplacementLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveReplacementLedger_round_trip x).symm
      (Eq.trans hread (effectiveReplacementLedger_round_trip y)))

instance effectiveReplacementLedgerBHistCarrier : BHistCarrier EffectiveReplacementLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveReplacementLedgerToEventFlow
  fromEventFlow := effectiveReplacementLedgerFromEventFlow

instance effectiveReplacementLedgerChapterTasteGate :
    ChapterTasteGate EffectiveReplacementLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveReplacementLedgerFromEventFlow (effectiveReplacementLedgerToEventFlow x) =
      some x
    exact effectiveReplacementLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveReplacementLedgerToEventFlow_injective heq)

def effectiveReplacementLedgerFields : EffectiveReplacementLedgerUp -> List BHist
  | EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport axiomPurity
      transport continuation provenance name =>
      [choiceWitness, quotientTransport, propextTransport, axiomPurity, transport,
        continuation, provenance, name]

private theorem effectiveReplacementLedger_field_faithful :
    forall x y : EffectiveReplacementLedgerUp,
      effectiveReplacementLedgerFields x = effectiveReplacementLedgerFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk choiceWitness1 quotientTransport1 propextTransport1 axiomPurity1 transport1
      continuation1 provenance1 name1 =>
      cases y with
      | mk choiceWitness2 quotientTransport2 propextTransport2 axiomPurity2 transport2
          continuation2 provenance2 name2 =>
          cases h
          rfl

private def effectiveReplacementLedgerFieldFaithfulConcrete :
    @FieldFaithful EffectiveReplacementLedgerUp effectiveReplacementLedgerBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveReplacementLedgerFields
  field_faithful := effectiveReplacementLedger_field_faithful

instance effectiveReplacementLedgerFieldFaithful :
    FieldFaithful EffectiveReplacementLedgerUp :=
  effectiveReplacementLedgerFieldFaithfulConcrete

theorem EffectiveReplacementLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
        effectiveReplacementLedgerDecodeBHist (effectiveReplacementLedgerEncodeBHist h) = h) /\
      (forall x : EffectiveReplacementLedgerUp,
        effectiveReplacementLedgerFromEventFlow (effectiveReplacementLedgerToEventFlow x) = some x) /\
        (forall x y : EffectiveReplacementLedgerUp,
          effectiveReplacementLedgerToEventFlow x = effectiveReplacementLedgerToEventFlow y ->
            x = y) /\
          effectiveReplacementLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact effectiveReplacementLedgerDecode_encode_bhist
  · constructor
    · exact effectiveReplacementLedger_round_trip
    · constructor
      · intro x y heq
        exact effectiveReplacementLedgerToEventFlow_injective heq
      · rfl

theorem EffectiveReplacementLedgerChoiceRow
    (choiceWitness quotientTransport propextTransport axiomPurity transport continuation
      provenance name : BHist) :
    effectiveReplacementLedgerFields
        (EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport
          axiomPurity transport continuation provenance name) =
          [choiceWitness, quotientTransport, propextTransport, axiomPurity, transport,
            continuation, provenance, name] /\
      Cont choiceWitness continuation (append choiceWitness continuation) /\
        hsame (append choiceWitness continuation) (append choiceWitness continuation) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem EffectiveReplacementLedgerQuotTransportRow
    (choiceWitness quotientTransport propextTransport axiomPurity transport continuation
      provenance name : BHist) :
    effectiveReplacementLedgerFields
        (EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport
          axiomPurity transport continuation provenance name) =
          [choiceWitness, quotientTransport, propextTransport, axiomPurity, transport,
            continuation, provenance, name] /\
      Cont quotientTransport transport (append quotientTransport transport) /\
        hsame (append quotientTransport transport) (append quotientTransport transport) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem EffectiveReplacementLedgerPropextTransportRow
    (choiceWitness quotientTransport propextTransport axiomPurity transport continuation
      provenance name : BHist) :
    effectiveReplacementLedgerFields
        (EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport
          axiomPurity transport continuation provenance name) =
          [choiceWitness, quotientTransport, propextTransport, axiomPurity, transport,
            continuation, provenance, name] /\
      Cont propextTransport continuation (append propextTransport continuation) /\
        hsame (append propextTransport continuation)
          (append propextTransport continuation) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem EffectiveReplacementLedgerAxiomPurityBoundary
    (choiceWitness quotientTransport propextTransport axiomPurity transport continuation
      provenance name hostTail : BHist) :
    effectiveReplacementLedgerFields
        (EffectiveReplacementLedgerUp.mk choiceWitness quotientTransport propextTransport
          axiomPurity transport continuation provenance name) =
          [choiceWitness, quotientTransport, propextTransport, axiomPurity, transport,
            continuation, provenance, name] /\
      Cont axiomPurity continuation (append axiomPurity continuation) /\
        hsame (append axiomPurity continuation) (append axiomPurity continuation) /\
          (Cont (append axiomPurity continuation) (BHist.e0 hostTail) axiomPurity ->
            False) /\
            (Cont (append axiomPurity continuation) (BHist.e1 hostTail) axiomPurity ->
              False) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · intro back
          exact cont_mutual_extension_right_tail_absurd.left rfl back
        · intro back
          exact cont_mutual_extension_right_tail_absurd.right rfl back

def EffectiveReplacementLedgerCarrier (x : EffectiveReplacementLedgerUp) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  exists W Q T A H C P N : BHist,
    x = EffectiveReplacementLedgerUp.mk W Q T A H C P N /\
      effectiveReplacementLedgerFields x = [W, Q, T, A, H, C, P, N] /\
        Cont W C (append W C) /\
          Cont Q H (append Q H) /\
            Cont T C (append T C) /\
              hsame A A

theorem EffectiveReplacementLedgerCarrier_admits_mk
    (W Q T A H C P N : BHist) :
    EffectiveReplacementLedgerCarrier
      (EffectiveReplacementLedgerUp.mk W Q T A H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨W, Q, T, A, H, C, P, N, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.EffectiveReplacementLedgerUp
