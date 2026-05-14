import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OracleSubstrateBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OracleSubstrateBoundaryUp : Type where
  | mk :
      (substrate oracleQuery externalChannel refusalLedger localObservation transport route
        provenance nameCert : BHist) →
      OracleSubstrateBoundaryUp
  deriving DecidableEq

def oracleSubstrateBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oracleSubstrateBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oracleSubstrateBoundaryEncodeBHist h

def oracleSubstrateBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oracleSubstrateBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oracleSubstrateBoundaryDecodeBHist tail)

private theorem oracleSubstrateBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      oracleSubstrateBoundaryDecodeBHist (oracleSubstrateBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem oracleSubstrateBoundary_mk_congr
    {substrate substrate' oracleQuery oracleQuery' externalChannel externalChannel'
      refusalLedger refusalLedger' localObservation localObservation' transport transport'
      route route' provenance provenance' nameCert nameCert' : BHist}
    (hSubstrate : substrate' = substrate)
    (hOracleQuery : oracleQuery' = oracleQuery)
    (hExternalChannel : externalChannel' = externalChannel)
    (hRefusalLedger : refusalLedger' = refusalLedger)
    (hLocalObservation : localObservation' = localObservation)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    OracleSubstrateBoundaryUp.mk substrate' oracleQuery' externalChannel' refusalLedger'
        localObservation' transport' route' provenance' nameCert' =
      OracleSubstrateBoundaryUp.mk substrate oracleQuery externalChannel refusalLedger
        localObservation transport route provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSubstrate
  cases hOracleQuery
  cases hExternalChannel
  cases hRefusalLedger
  cases hLocalObservation
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

def oracleSubstrateBoundaryFields : OracleSubstrateBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OracleSubstrateBoundaryUp.mk substrate oracleQuery externalChannel refusalLedger
      localObservation transport route provenance nameCert =>
      [substrate, oracleQuery, externalChannel, refusalLedger, localObservation, transport,
        route, provenance, nameCert]

def oracleSubstrateBoundaryToEventFlow : OracleSubstrateBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (oracleSubstrateBoundaryFields x).map oracleSubstrateBoundaryEncodeBHist

def oracleSubstrateBoundaryFromEventFlow :
    EventFlow → Option OracleSubstrateBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | substrate :: rest0 =>
      match rest0 with
      | [] => none
      | oracleQuery :: rest1 =>
          match rest1 with
          | [] => none
          | externalChannel :: rest2 =>
              match rest2 with
              | [] => none
              | refusalLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | localObservation :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (OracleSubstrateBoundaryUp.mk
                                              (oracleSubstrateBoundaryDecodeBHist substrate)
                                              (oracleSubstrateBoundaryDecodeBHist oracleQuery)
                                              (oracleSubstrateBoundaryDecodeBHist externalChannel)
                                              (oracleSubstrateBoundaryDecodeBHist refusalLedger)
                                              (oracleSubstrateBoundaryDecodeBHist localObservation)
                                              (oracleSubstrateBoundaryDecodeBHist transport)
                                              (oracleSubstrateBoundaryDecodeBHist route)
                                              (oracleSubstrateBoundaryDecodeBHist provenance)
                                              (oracleSubstrateBoundaryDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem oracleSubstrateBoundary_round_trip :
    ∀ x : OracleSubstrateBoundaryUp,
      oracleSubstrateBoundaryFromEventFlow
        (oracleSubstrateBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk substrate oracleQuery externalChannel refusalLedger localObservation transport route
      provenance nameCert =>
      change
        some
          (OracleSubstrateBoundaryUp.mk
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist substrate))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist oracleQuery))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist externalChannel))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist refusalLedger))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist localObservation))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist transport))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist route))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist provenance))
            (oracleSubstrateBoundaryDecodeBHist
              (oracleSubstrateBoundaryEncodeBHist nameCert))) =
          some
            (OracleSubstrateBoundaryUp.mk substrate oracleQuery externalChannel refusalLedger
              localObservation transport route provenance nameCert)
      exact
        congrArg some
          (oracleSubstrateBoundary_mk_congr
            (oracleSubstrateBoundaryDecode_encode_bhist substrate)
            (oracleSubstrateBoundaryDecode_encode_bhist oracleQuery)
            (oracleSubstrateBoundaryDecode_encode_bhist externalChannel)
            (oracleSubstrateBoundaryDecode_encode_bhist refusalLedger)
            (oracleSubstrateBoundaryDecode_encode_bhist localObservation)
            (oracleSubstrateBoundaryDecode_encode_bhist transport)
            (oracleSubstrateBoundaryDecode_encode_bhist route)
            (oracleSubstrateBoundaryDecode_encode_bhist provenance)
            (oracleSubstrateBoundaryDecode_encode_bhist nameCert))

private theorem oracleSubstrateBoundaryToEventFlow_injective
    {x y : OracleSubstrateBoundaryUp} :
    oracleSubstrateBoundaryToEventFlow x =
      oracleSubstrateBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oracleSubstrateBoundaryFromEventFlow
          (oracleSubstrateBoundaryToEventFlow x) =
        oracleSubstrateBoundaryFromEventFlow
          (oracleSubstrateBoundaryToEventFlow y) :=
    congrArg oracleSubstrateBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (oracleSubstrateBoundary_round_trip x).symm
      (Eq.trans hread (oracleSubstrateBoundary_round_trip y)))

private theorem oracleSubstrateBoundary_fields_faithful :
    ∀ x y : OracleSubstrateBoundaryUp,
      oracleSubstrateBoundaryFields x = oracleSubstrateBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk substrate₁ oracleQuery₁ externalChannel₁ refusalLedger₁ localObservation₁ transport₁
      route₁ provenance₁ nameCert₁ =>
      cases y with
      | mk substrate₂ oracleQuery₂ externalChannel₂ refusalLedger₂ localObservation₂
          transport₂ route₂ provenance₂ nameCert₂ =>
          simp only [oracleSubstrateBoundaryFields] at h
          cases h
          rfl

instance oracleSubstrateBoundaryBHistCarrier :
    BHistCarrier OracleSubstrateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oracleSubstrateBoundaryToEventFlow
  fromEventFlow := oracleSubstrateBoundaryFromEventFlow

instance oracleSubstrateBoundaryChapterTasteGate :
    ChapterTasteGate OracleSubstrateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      oracleSubstrateBoundaryFromEventFlow
        (oracleSubstrateBoundaryToEventFlow x) = some x
    exact oracleSubstrateBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (oracleSubstrateBoundaryToEventFlow_injective heq)

instance oracleSubstrateBoundaryFieldFaithful :
    FieldFaithful OracleSubstrateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := oracleSubstrateBoundaryFields
  field_faithful := oracleSubstrateBoundary_fields_faithful

theorem OracleSubstrateBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      oracleSubstrateBoundaryDecodeBHist (oracleSubstrateBoundaryEncodeBHist h) = h) ∧
      (∀ x : OracleSubstrateBoundaryUp,
        oracleSubstrateBoundaryFromEventFlow
          (oracleSubstrateBoundaryToEventFlow x) = some x) ∧
        (∀ x y : OracleSubstrateBoundaryUp,
          oracleSubstrateBoundaryToEventFlow x =
            oracleSubstrateBoundaryToEventFlow y → x = y) ∧
          oracleSubstrateBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact oracleSubstrateBoundaryDecode_encode_bhist
  · constructor
    · exact oracleSubstrateBoundary_round_trip
    · constructor
      · intro x y heq
        exact oracleSubstrateBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.OracleSubstrateBoundaryUp
