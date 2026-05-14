import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverInterfaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverInterfaceUp : Type where
  | mk :
      (history filter attention selected omitted licensed stream noSubject transports ledger
        routes provenance name : BHist) →
        ObserverInterfaceUp
  deriving DecidableEq

def observerInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerInterfaceEncodeBHist h

def observerInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerInterfaceDecodeBHist tail)

private theorem observerInterfaceDecode_encode_bhist :
    ∀ h : BHist, observerInterfaceDecodeBHist (observerInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem observerInterface_mk_congr
    {history history' filter filter' attention attention' selected selected' omitted omitted'
      licensed licensed' stream stream' noSubject noSubject' transports transports' ledger
      ledger' routes routes' provenance provenance' name name' : BHist}
    (hHistory : history' = history)
    (hFilter : filter' = filter)
    (hAttention : attention' = attention)
    (hSelected : selected' = selected)
    (hOmitted : omitted' = omitted)
    (hLicensed : licensed' = licensed)
    (hStream : stream' = stream)
    (hNoSubject : noSubject' = noSubject)
    (hTransports : transports' = transports)
    (hLedger : ledger' = ledger)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ObserverInterfaceUp.mk history' filter' attention' selected' omitted' licensed' stream'
        noSubject' transports' ledger' routes' provenance' name' =
      ObserverInterfaceUp.mk history filter attention selected omitted licensed stream noSubject
        transports ledger routes provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hHistory
  cases hFilter
  cases hAttention
  cases hSelected
  cases hOmitted
  cases hLicensed
  cases hStream
  cases hNoSubject
  cases hTransports
  cases hLedger
  cases hRoutes
  cases hProvenance
  cases hName
  rfl

def observerInterfaceToEventFlow : ObserverInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverInterfaceUp.mk history filter attention selected omitted licensed stream noSubject
      transports ledger routes provenance name =>
      [[BMark.b0], observerInterfaceEncodeBHist history, [BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist filter, [BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist attention, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist selected,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist omitted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist licensed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerInterfaceEncodeBHist noSubject,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerInterfaceEncodeBHist name]

def observerInterfaceFromEventFlow : EventFlow → Option ObserverInterfaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | filter :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | attention :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | selected :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | omitted :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | licensed :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | stream :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | noSubject :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transports ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | ledger ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] =>
                                                                                          none
                                                                                      | routes ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22 with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | provenance ::
                                                                                                  rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | name ::
                                                                                                          rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (ObserverInterfaceUp.mk
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    history)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    filter)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    attention)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    selected)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    omitted)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    licensed)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    stream)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    noSubject)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    transports)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    ledger)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    routes)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (observerInterfaceDecodeBHist
                                                                                                                    name))
                                                                                                          | _ :: _ =>
                                                                                                              none

private theorem observerInterface_round_trip :
    ∀ x : ObserverInterfaceUp,
      observerInterfaceFromEventFlow (observerInterfaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history filter attention selected omitted licensed stream noSubject transports ledger
      routes provenance name =>
      change
        some
          (ObserverInterfaceUp.mk
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist history))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist filter))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist attention))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist selected))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist omitted))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist licensed))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist stream))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist noSubject))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist transports))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist ledger))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist routes))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist provenance))
            (observerInterfaceDecodeBHist (observerInterfaceEncodeBHist name))) =
          some
            (ObserverInterfaceUp.mk history filter attention selected omitted licensed stream
              noSubject transports ledger routes provenance name)
      exact
        congrArg some
          (observerInterface_mk_congr
            (observerInterfaceDecode_encode_bhist history)
            (observerInterfaceDecode_encode_bhist filter)
            (observerInterfaceDecode_encode_bhist attention)
            (observerInterfaceDecode_encode_bhist selected)
            (observerInterfaceDecode_encode_bhist omitted)
            (observerInterfaceDecode_encode_bhist licensed)
            (observerInterfaceDecode_encode_bhist stream)
            (observerInterfaceDecode_encode_bhist noSubject)
            (observerInterfaceDecode_encode_bhist transports)
            (observerInterfaceDecode_encode_bhist ledger)
            (observerInterfaceDecode_encode_bhist routes)
            (observerInterfaceDecode_encode_bhist provenance)
            (observerInterfaceDecode_encode_bhist name))

private theorem observerInterfaceToEventFlow_injective {x y : ObserverInterfaceUp} :
    observerInterfaceToEventFlow x = observerInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerInterfaceFromEventFlow (observerInterfaceToEventFlow x) =
        observerInterfaceFromEventFlow (observerInterfaceToEventFlow y) :=
    congrArg observerInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerInterface_round_trip x).symm
      (Eq.trans hread (observerInterface_round_trip y)))

instance observerInterfaceBHistCarrier : BHistCarrier ObserverInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerInterfaceToEventFlow
  fromEventFlow := observerInterfaceFromEventFlow

instance observerInterfaceChapterTasteGate : ChapterTasteGate ObserverInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerInterfaceFromEventFlow (observerInterfaceToEventFlow x) = some x
    exact observerInterface_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerInterfaceToEventFlow_injective heq)

instance observerInterfaceFieldFaithful : FieldFaithful ObserverInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverInterfaceUp.mk history filter attention selected omitted licensed stream noSubject
        transports ledger routes provenance name =>
        [history, filter, attention, selected, omitted, licensed, stream, noSubject,
          transports, ledger, routes, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk history₁ filter₁ attention₁ selected₁ omitted₁ licensed₁ stream₁ noSubject₁
        transports₁ ledger₁ routes₁ provenance₁ name₁ =>
        cases y with
        | mk history₂ filter₂ attention₂ selected₂ omitted₂ licensed₂ stream₂ noSubject₂
            transports₂ ledger₂ routes₂ provenance₂ name₂ =>
            cases h
            rfl

def taste_gate : ChapterTasteGate ObserverInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerInterfaceChapterTasteGate

theorem ObserverInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerInterfaceDecodeBHist (observerInterfaceEncodeBHist h) = h) ∧
      (∀ x : ObserverInterfaceUp,
        observerInterfaceFromEventFlow (observerInterfaceToEventFlow x) = some x) ∧
        (∀ x y : ObserverInterfaceUp,
          observerInterfaceToEventFlow x = observerInterfaceToEventFlow y → x = y) ∧
          observerInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerInterfaceDecode_encode_bhist
  · constructor
    · exact observerInterface_round_trip
    · constructor
      · intro x y heq
        exact observerInterfaceToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverInterfaceUp.TasteGate
