import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionGapLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionGapLedgerUp : Type where
  | mk :
      (source name route check consumer residue transport continuation provenance
        localName : BHist) →
      InscriptionGapLedgerUp
  deriving DecidableEq

def inscriptionGapLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionGapLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionGapLedgerEncodeBHist h

def inscriptionGapLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionGapLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionGapLedgerDecodeBHist tail)

private theorem inscriptionGapLedger_decode_encode_bhist :
    ∀ h : BHist, inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscriptionGapLedger_mk_congr
    {source source' name name' route route' check check' consumer consumer'
      residue residue' transport transport' continuation continuation'
      provenance provenance' localName localName' : BHist}
    (hSource : source' = source)
    (hName : name' = name)
    (hRoute : route' = route)
    (hCheck : check' = check)
    (hConsumer : consumer' = consumer)
    (hResidue : residue' = residue)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    InscriptionGapLedgerUp.mk source' name' route' check' consumer' residue'
        transport' continuation' provenance' localName' =
      InscriptionGapLedgerUp.mk source name route check consumer residue transport
        continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hName
  cases hRoute
  cases hCheck
  cases hConsumer
  cases hResidue
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def inscriptionGapLedgerToEventFlow : InscriptionGapLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionGapLedgerUp.mk source name route check consumer residue transport
      continuation provenance localName =>
      [[BMark.b0],
        inscriptionGapLedgerEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionGapLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionGapLedgerEncodeBHist localName]

def inscriptionGapLedgerFromEventFlow : EventFlow → Option InscriptionGapLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | name :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | check :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | consumer :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | residue :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscriptionGapLedgerUp.mk
                                                                                          (inscriptionGapLedgerDecodeBHist source)
                                                                                          (inscriptionGapLedgerDecodeBHist name)
                                                                                          (inscriptionGapLedgerDecodeBHist route)
                                                                                          (inscriptionGapLedgerDecodeBHist check)
                                                                                          (inscriptionGapLedgerDecodeBHist consumer)
                                                                                          (inscriptionGapLedgerDecodeBHist residue)
                                                                                          (inscriptionGapLedgerDecodeBHist transport)
                                                                                          (inscriptionGapLedgerDecodeBHist continuation)
                                                                                          (inscriptionGapLedgerDecodeBHist provenance)
                                                                                          (inscriptionGapLedgerDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem inscriptionGapLedger_round_trip :
    ∀ x : InscriptionGapLedgerUp,
      inscriptionGapLedgerFromEventFlow (inscriptionGapLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source name route check consumer residue transport continuation provenance localName =>
      change
        some
          (InscriptionGapLedgerUp.mk
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist source))
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist name))
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist route))
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist check))
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist consumer))
            (inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist residue))
            (inscriptionGapLedgerDecodeBHist
              (inscriptionGapLedgerEncodeBHist transport))
            (inscriptionGapLedgerDecodeBHist
              (inscriptionGapLedgerEncodeBHist continuation))
            (inscriptionGapLedgerDecodeBHist
              (inscriptionGapLedgerEncodeBHist provenance))
            (inscriptionGapLedgerDecodeBHist
              (inscriptionGapLedgerEncodeBHist localName))) =
          some
            (InscriptionGapLedgerUp.mk source name route check consumer residue transport
              continuation provenance localName)
      exact
        congrArg some
          (inscriptionGapLedger_mk_congr
            (inscriptionGapLedger_decode_encode_bhist source)
            (inscriptionGapLedger_decode_encode_bhist name)
            (inscriptionGapLedger_decode_encode_bhist route)
            (inscriptionGapLedger_decode_encode_bhist check)
            (inscriptionGapLedger_decode_encode_bhist consumer)
            (inscriptionGapLedger_decode_encode_bhist residue)
            (inscriptionGapLedger_decode_encode_bhist transport)
            (inscriptionGapLedger_decode_encode_bhist continuation)
            (inscriptionGapLedger_decode_encode_bhist provenance)
            (inscriptionGapLedger_decode_encode_bhist localName))

private theorem inscriptionGapLedgerToEventFlow_injective
    {x y : InscriptionGapLedgerUp} :
    inscriptionGapLedgerToEventFlow x = inscriptionGapLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionGapLedgerFromEventFlow (inscriptionGapLedgerToEventFlow x) =
        inscriptionGapLedgerFromEventFlow (inscriptionGapLedgerToEventFlow y) :=
    congrArg inscriptionGapLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionGapLedger_round_trip x).symm
      (Eq.trans hread (inscriptionGapLedger_round_trip y)))

instance inscriptionGapLedgerBHistCarrier : BHistCarrier InscriptionGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionGapLedgerToEventFlow
  fromEventFlow := inscriptionGapLedgerFromEventFlow

instance inscriptionGapLedgerChapterTasteGate : ChapterTasteGate InscriptionGapLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscriptionGapLedgerFromEventFlow (inscriptionGapLedgerToEventFlow x) = some x
    exact inscriptionGapLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionGapLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate InscriptionGapLedgerUp :=
  inscriptionGapLedgerChapterTasteGate

theorem InscriptionGapLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, inscriptionGapLedgerDecodeBHist (inscriptionGapLedgerEncodeBHist h) = h) ∧
      (∀ x : InscriptionGapLedgerUp,
        inscriptionGapLedgerFromEventFlow (inscriptionGapLedgerToEventFlow x) = some x) ∧
        (∀ x y : InscriptionGapLedgerUp,
          inscriptionGapLedgerToEventFlow x = inscriptionGapLedgerToEventFlow y → x = y) ∧
          inscriptionGapLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionGapLedger_decode_encode_bhist
  · constructor
    · exact inscriptionGapLedger_round_trip
    · constructor
      · intro x y heq
        exact inscriptionGapLedgerToEventFlow_injective heq
      · rfl

theorem InscriptionGapLedger_source_boundary :
    ∀ source name route check consumer residue transport continuation provenance localName : BHist,
      let packet :=
        InscriptionGapLedgerUp.mk source name route check consumer residue transport continuation
          provenance localName
      BEDC.FKernel.Cont.Cont source route (BEDC.FKernel.Cont.append source route) ∧
        hsame check check ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow packet) = some packet := by
  -- BEDC touchpoint anchor: BHist BMark
  intro source name route check consumer residue transport continuation provenance localName
  constructor
  · rfl
  · constructor
    · exact hsame_refl check
    · change
        inscriptionGapLedgerFromEventFlow
            (inscriptionGapLedgerToEventFlow
              (InscriptionGapLedgerUp.mk source name route check consumer residue transport
                continuation provenance localName)) =
          some
            (InscriptionGapLedgerUp.mk source name route check consumer residue transport
              continuation provenance localName)
      exact inscriptionGapLedger_round_trip
        (InscriptionGapLedgerUp.mk source name route check consumer residue transport
          continuation provenance localName)

end BEDC.Derived.InscriptionGapLedgerUp
