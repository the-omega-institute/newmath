import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSupportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSupportUp : Type where
  | mk :
      (objectSupport homSupport ledger transport route provenance name : BHist) →
      FiniteSupportUp

def finiteSupportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSupportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSupportEncodeBHist h

def finiteSupportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSupportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSupportDecodeBHist tail)

private theorem finiteSupportDecode_encode_bhist :
    ∀ h : BHist,
      finiteSupportDecodeBHist (finiteSupportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem finiteSupport_mk_congr
    {objectSupport objectSupport' homSupport homSupport' ledger ledger' transport
      transport' route route' provenance provenance' name name' : BHist}
    (hObjectSupport : objectSupport' = objectSupport)
    (hHomSupport : homSupport' = homSupport)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FiniteSupportUp.mk objectSupport' homSupport' ledger' transport' route' provenance'
        name' =
      FiniteSupportUp.mk objectSupport homSupport ledger transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObjectSupport
  cases hHomSupport
  cases hLedger
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def finiteSupportToEventFlow : FiniteSupportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSupportUp.mk objectSupport homSupport ledger transport route provenance name =>
      [[BMark.b0],
        finiteSupportEncodeBHist objectSupport,
        [BMark.b1, BMark.b0],
        finiteSupportEncodeBHist homSupport,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteSupportEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSupportEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSupportEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSupportEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteSupportEncodeBHist name]

def finiteSupportFromEventFlow : EventFlow → Option FiniteSupportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | objectSupport :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | homSupport :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (FiniteSupportUp.mk
                                                                  (finiteSupportDecodeBHist
                                                                    objectSupport)
                                                                  (finiteSupportDecodeBHist
                                                                    homSupport)
                                                                  (finiteSupportDecodeBHist
                                                                    ledger)
                                                                  (finiteSupportDecodeBHist
                                                                    transport)
                                                                  (finiteSupportDecodeBHist
                                                                    route)
                                                                  (finiteSupportDecodeBHist
                                                                    provenance)
                                                                  (finiteSupportDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem finiteSupport_round_trip :
    ∀ x : FiniteSupportUp,
      finiteSupportFromEventFlow (finiteSupportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk objectSupport homSupport ledger transport route provenance name =>
      change
        some
          (FiniteSupportUp.mk
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist objectSupport))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist homSupport))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist ledger))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist transport))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist route))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist provenance))
            (finiteSupportDecodeBHist (finiteSupportEncodeBHist name))) =
          some
            (FiniteSupportUp.mk objectSupport homSupport ledger transport route provenance
              name)
      exact
        congrArg some
          (finiteSupport_mk_congr
            (finiteSupportDecode_encode_bhist objectSupport)
            (finiteSupportDecode_encode_bhist homSupport)
            (finiteSupportDecode_encode_bhist ledger)
            (finiteSupportDecode_encode_bhist transport)
            (finiteSupportDecode_encode_bhist route)
            (finiteSupportDecode_encode_bhist provenance)
            (finiteSupportDecode_encode_bhist name))

private theorem finiteSupportToEventFlow_injective {x y : FiniteSupportUp} :
    finiteSupportToEventFlow x = finiteSupportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSupportFromEventFlow (finiteSupportToEventFlow x) =
        finiteSupportFromEventFlow (finiteSupportToEventFlow y) :=
    congrArg finiteSupportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteSupport_round_trip x).symm
      (Eq.trans hread (finiteSupport_round_trip y)))

instance finiteSupportBHistCarrier : BHistCarrier FiniteSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSupportToEventFlow
  fromEventFlow := finiteSupportFromEventFlow

instance finiteSupportChapterTasteGate : ChapterTasteGate FiniteSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSupportFromEventFlow (finiteSupportToEventFlow x) = some x
    exact finiteSupport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteSupportToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteSupportUp :=
  finiteSupportChapterTasteGate

instance finiteSupportFieldFaithful : FieldFaithful FiniteSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteSupportUp.mk objectSupport homSupport ledger transport route provenance name =>
        [objectSupport, homSupport, ledger, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk objectSupport1 homSupport1 ledger1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk objectSupport2 homSupport2 ledger2 transport2 route2 provenance2 name2 =>
            injection h with hObjectSupport t1
            injection t1 with hHomSupport t2
            injection t2 with hLedger t3
            injection t3 with hTransport t4
            injection t4 with hRoute t5
            injection t5 with hProvenance t6
            injection t6 with hName _
            cases hObjectSupport
            cases hHomSupport
            cases hLedger
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem FiniteSupportTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteSupportDecodeBHist (finiteSupportEncodeBHist h) = h) ∧
      (∀ x : FiniteSupportUp,
        finiteSupportFromEventFlow (finiteSupportToEventFlow x) = some x) ∧
        (∀ x y : FiniteSupportUp,
          finiteSupportToEventFlow x = finiteSupportToEventFlow y -> x = y) ∧
          finiteSupportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteSupportDecode_encode_bhist
  · constructor
    · exact finiteSupport_round_trip
    · constructor
      · intro x y heq
        exact finiteSupportToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteSupportUp
