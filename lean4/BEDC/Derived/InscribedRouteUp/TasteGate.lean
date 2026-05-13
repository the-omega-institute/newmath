import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscribedRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscribedRouteUp : Type where
  | mk :
      (source gap statement route acceptance consumer ledger provenance name : BHist) →
      InscribedRouteUp
  deriving DecidableEq

private def inscribedRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscribedRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscribedRouteEncodeBHist h

private def inscribedRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscribedRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscribedRouteDecodeBHist tail)

private theorem inscribedRouteDecode_encode_bhist :
    ∀ h : BHist, inscribedRouteDecodeBHist (inscribedRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscribedRoute_mk_congr
    {source source' gap gap' statement statement' route route' acceptance acceptance'
      consumer consumer' ledger ledger' provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hGap : gap' = gap)
    (hStatement : statement' = statement)
    (hRoute : route' = route)
    (hAcceptance : acceptance' = acceptance)
    (hConsumer : consumer' = consumer)
    (hLedger : ledger' = ledger)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    InscribedRouteUp.mk source' gap' statement' route' acceptance' consumer' ledger'
        provenance' name' =
      InscribedRouteUp.mk source gap statement route acceptance consumer ledger provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hGap
  cases hStatement
  cases hRoute
  cases hAcceptance
  cases hConsumer
  cases hLedger
  cases hProvenance
  cases hName
  rfl

private def inscribedRouteToEventFlow : InscribedRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscribedRouteUp.mk source gap statement route acceptance consumer ledger provenance name =>
      [[BMark.b0],
        inscribedRouteEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist statement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist acceptance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscribedRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscribedRouteEncodeBHist name]

private def inscribedRouteFromEventFlow : EventFlow → Option InscribedRouteUp
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
              | gap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | statement :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | acceptance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consumer :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (InscribedRouteUp.mk
                                                                                  (inscribedRouteDecodeBHist source)
                                                                                  (inscribedRouteDecodeBHist gap)
                                                                                  (inscribedRouteDecodeBHist statement)
                                                                                  (inscribedRouteDecodeBHist route)
                                                                                  (inscribedRouteDecodeBHist acceptance)
                                                                                  (inscribedRouteDecodeBHist consumer)
                                                                                  (inscribedRouteDecodeBHist ledger)
                                                                                  (inscribedRouteDecodeBHist provenance)
                                                                                  (inscribedRouteDecodeBHist name))
                                                                          | _ :: _ => none

private theorem inscribedRoute_round_trip :
    ∀ x : InscribedRouteUp,
      inscribedRouteFromEventFlow (inscribedRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source gap statement route acceptance consumer ledger provenance name =>
      change
        some
          (InscribedRouteUp.mk
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist source))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist gap))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist statement))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist route))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist acceptance))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist consumer))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist ledger))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist provenance))
            (inscribedRouteDecodeBHist (inscribedRouteEncodeBHist name))) =
          some
            (InscribedRouteUp.mk source gap statement route acceptance consumer ledger
              provenance name)
      exact
        congrArg some
          (inscribedRoute_mk_congr
            (inscribedRouteDecode_encode_bhist source)
            (inscribedRouteDecode_encode_bhist gap)
            (inscribedRouteDecode_encode_bhist statement)
            (inscribedRouteDecode_encode_bhist route)
            (inscribedRouteDecode_encode_bhist acceptance)
            (inscribedRouteDecode_encode_bhist consumer)
            (inscribedRouteDecode_encode_bhist ledger)
            (inscribedRouteDecode_encode_bhist provenance)
            (inscribedRouteDecode_encode_bhist name))

private theorem inscribedRouteToEventFlow_injective {x y : InscribedRouteUp} :
    inscribedRouteToEventFlow x = inscribedRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscribedRouteFromEventFlow (inscribedRouteToEventFlow x) =
        inscribedRouteFromEventFlow (inscribedRouteToEventFlow y) :=
    congrArg inscribedRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscribedRoute_round_trip x).symm
      (Eq.trans hread (inscribedRoute_round_trip y)))

instance inscribedRouteBHistCarrier : BHistCarrier InscribedRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscribedRouteToEventFlow
  fromEventFlow := inscribedRouteFromEventFlow

instance inscribedRouteChapterTasteGate : ChapterTasteGate InscribedRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscribedRouteFromEventFlow (inscribedRouteToEventFlow x) = some x
    exact inscribedRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscribedRouteToEventFlow_injective heq)

theorem InscribedRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist, inscribedRouteDecodeBHist (inscribedRouteEncodeBHist h) = h) ∧
      (∀ x : InscribedRouteUp,
        inscribedRouteFromEventFlow (inscribedRouteToEventFlow x) = some x) ∧
        (∀ x y : InscribedRouteUp,
          inscribedRouteToEventFlow x = inscribedRouteToEventFlow y → x = y) ∧
          inscribedRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscribedRouteDecode_encode_bhist
  · constructor
    · exact inscribedRoute_round_trip
    · constructor
      · intro x y heq
        exact inscribedRouteToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscribedRouteUp
