import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionAcceptanceBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionAcceptanceBudgetUp : Type where
  | mk (source name route check consumer budget residue transports routes provenance
      localName : BHist) : InscriptionAcceptanceBudgetUp
  deriving DecidableEq

def inscriptionAcceptanceBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionAcceptanceBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionAcceptanceBudgetEncodeBHist h

def inscriptionAcceptanceBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionAcceptanceBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionAcceptanceBudgetDecodeBHist tail)

private theorem inscriptionAcceptanceBudgetDecode_encode_bhist :
    ∀ h : BHist,
      inscriptionAcceptanceBudgetDecodeBHist (inscriptionAcceptanceBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscriptionAcceptanceBudget_mk_congr
    {source source' name name' route route' check check' consumer consumer' budget budget'
      residue residue' transports transports' routes routes' provenance provenance'
      localName localName' : BHist}
    (hSource : source' = source)
    (hName : name' = name)
    (hRoute : route' = route)
    (hCheck : check' = check)
    (hConsumer : consumer' = consumer)
    (hBudget : budget' = budget)
    (hResidue : residue' = residue)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    InscriptionAcceptanceBudgetUp.mk source' name' route' check' consumer' budget' residue'
        transports' routes' provenance' localName' =
      InscriptionAcceptanceBudgetUp.mk source name route check consumer budget residue transports
        routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hName
  cases hRoute
  cases hCheck
  cases hConsumer
  cases hBudget
  cases hResidue
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

def inscriptionAcceptanceBudgetToEventFlow : InscriptionAcceptanceBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionAcceptanceBudgetUp.mk source name route check consumer budget residue transports
      routes provenance localName =>
      [[BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAcceptanceBudgetEncodeBHist localName]

def inscriptionAcceptanceBudgetFromEventFlow :
    EventFlow → Option InscriptionAcceptanceBudgetUp
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
                                              | budget :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | residue :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transports :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | localName :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (InscriptionAcceptanceBudgetUp.mk
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist source)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist name)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist route)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist check)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist consumer)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist budget)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist residue)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist transports)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist routes)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist provenance)
                                                                                                  (inscriptionAcceptanceBudgetDecodeBHist localName))
                                                                                          | _ :: _ => none

private theorem inscriptionAcceptanceBudget_round_trip :
    ∀ x : InscriptionAcceptanceBudgetUp,
      inscriptionAcceptanceBudgetFromEventFlow
        (inscriptionAcceptanceBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source name route check consumer budget residue transports routes provenance localName =>
      change
        some
          (InscriptionAcceptanceBudgetUp.mk
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist source))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist name))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist route))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist check))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist consumer))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist budget))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist residue))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist transports))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist routes))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist provenance))
            (inscriptionAcceptanceBudgetDecodeBHist
              (inscriptionAcceptanceBudgetEncodeBHist localName))) =
          some
            (InscriptionAcceptanceBudgetUp.mk source name route check consumer budget residue
              transports routes provenance localName)
      exact
        congrArg some
          (inscriptionAcceptanceBudget_mk_congr
            (inscriptionAcceptanceBudgetDecode_encode_bhist source)
            (inscriptionAcceptanceBudgetDecode_encode_bhist name)
            (inscriptionAcceptanceBudgetDecode_encode_bhist route)
            (inscriptionAcceptanceBudgetDecode_encode_bhist check)
            (inscriptionAcceptanceBudgetDecode_encode_bhist consumer)
            (inscriptionAcceptanceBudgetDecode_encode_bhist budget)
            (inscriptionAcceptanceBudgetDecode_encode_bhist residue)
            (inscriptionAcceptanceBudgetDecode_encode_bhist transports)
            (inscriptionAcceptanceBudgetDecode_encode_bhist routes)
            (inscriptionAcceptanceBudgetDecode_encode_bhist provenance)
            (inscriptionAcceptanceBudgetDecode_encode_bhist localName))

private theorem inscriptionAcceptanceBudgetToEventFlow_injective
    {x y : InscriptionAcceptanceBudgetUp} :
    inscriptionAcceptanceBudgetToEventFlow x =
      inscriptionAcceptanceBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionAcceptanceBudgetFromEventFlow
          (inscriptionAcceptanceBudgetToEventFlow x) =
        inscriptionAcceptanceBudgetFromEventFlow
          (inscriptionAcceptanceBudgetToEventFlow y) :=
    congrArg inscriptionAcceptanceBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionAcceptanceBudget_round_trip x).symm
      (Eq.trans hread (inscriptionAcceptanceBudget_round_trip y)))

instance inscriptionAcceptanceBudgetBHistCarrier :
    BHistCarrier InscriptionAcceptanceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionAcceptanceBudgetToEventFlow
  fromEventFlow := inscriptionAcceptanceBudgetFromEventFlow

instance inscriptionAcceptanceBudgetChapterTasteGate :
    ChapterTasteGate InscriptionAcceptanceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inscriptionAcceptanceBudgetFromEventFlow
        (inscriptionAcceptanceBudgetToEventFlow x) = some x
    exact inscriptionAcceptanceBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionAcceptanceBudgetToEventFlow_injective heq)

theorem InscriptionAcceptanceBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inscriptionAcceptanceBudgetDecodeBHist
        (inscriptionAcceptanceBudgetEncodeBHist h) = h) ∧
      (∀ x : InscriptionAcceptanceBudgetUp,
        inscriptionAcceptanceBudgetFromEventFlow
          (inscriptionAcceptanceBudgetToEventFlow x) = some x) ∧
        (∀ x y : InscriptionAcceptanceBudgetUp,
          inscriptionAcceptanceBudgetToEventFlow x =
            inscriptionAcceptanceBudgetToEventFlow y → x = y) ∧
          inscriptionAcceptanceBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionAcceptanceBudgetDecode_encode_bhist
  · constructor
    · exact inscriptionAcceptanceBudget_round_trip
    · constructor
      · intro x y heq
        exact inscriptionAcceptanceBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscriptionAcceptanceBudgetUp
