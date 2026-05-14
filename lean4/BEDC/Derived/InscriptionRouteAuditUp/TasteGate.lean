import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionRouteAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionRouteAuditUp : Type where
  | mk :
      (source gap route accepted downstream transport cont provenance name : BHist) →
      InscriptionRouteAuditUp
  deriving DecidableEq

def inscriptionRouteAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionRouteAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionRouteAuditEncodeBHist h

private def inscriptionRouteAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionRouteAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionRouteAuditDecodeBHist tail)

private theorem inscriptionRouteAuditDecode_encode_bhist :
    ∀ h : BHist,
      inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem inscriptionRouteAudit_mk_congr
    {source source' gap gap' route route' accepted accepted' downstream downstream'
      transport transport' cont cont' provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hGap : gap' = gap)
    (hRoute : route' = route)
    (hAccepted : accepted' = accepted)
    (hDownstream : downstream' = downstream)
    (hTransport : transport' = transport)
    (hCont : cont' = cont)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    InscriptionRouteAuditUp.mk source' gap' route' accepted' downstream' transport' cont'
        provenance' name' =
      InscriptionRouteAuditUp.mk source gap route accepted downstream transport cont
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hGap
  cases hRoute
  cases hAccepted
  cases hDownstream
  cases hTransport
  cases hCont
  cases hProvenance
  cases hName
  rfl

private def inscriptionRouteAuditToEventFlow : InscriptionRouteAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionRouteAuditUp.mk source gap route accepted downstream transport cont provenance
      name =>
      [[BMark.b0],
        inscriptionRouteAuditEncodeBHist source,
        [BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist accepted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist downstream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist cont,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionRouteAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionRouteAuditEncodeBHist name]

private def inscriptionRouteAuditFromEventFlow : EventFlow → Option InscriptionRouteAuditUp
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
                      | route :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | accepted :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | downstream :: rest9 =>
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
                                                      | cont :: rest13 =>
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
                                                                                (InscriptionRouteAuditUp.mk
                                                                                  (inscriptionRouteAuditDecodeBHist source)
                                                                                  (inscriptionRouteAuditDecodeBHist gap)
                                                                                  (inscriptionRouteAuditDecodeBHist route)
                                                                                  (inscriptionRouteAuditDecodeBHist accepted)
                                                                                  (inscriptionRouteAuditDecodeBHist downstream)
                                                                                  (inscriptionRouteAuditDecodeBHist transport)
                                                                                  (inscriptionRouteAuditDecodeBHist cont)
                                                                                  (inscriptionRouteAuditDecodeBHist provenance)
                                                                                  (inscriptionRouteAuditDecodeBHist name))
                                                                          | _ :: _ => none

private theorem inscriptionRouteAudit_round_trip :
    ∀ x : InscriptionRouteAuditUp,
      inscriptionRouteAuditFromEventFlow (inscriptionRouteAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source gap route accepted downstream transport cont provenance name =>
      change
        some
          (InscriptionRouteAuditUp.mk
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist source))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist gap))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist route))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist accepted))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist downstream))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist transport))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist cont))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist provenance))
            (inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist name))) =
          some
            (InscriptionRouteAuditUp.mk source gap route accepted downstream transport cont
              provenance name)
      exact
        congrArg some
          (inscriptionRouteAudit_mk_congr
            (inscriptionRouteAuditDecode_encode_bhist source)
            (inscriptionRouteAuditDecode_encode_bhist gap)
            (inscriptionRouteAuditDecode_encode_bhist route)
            (inscriptionRouteAuditDecode_encode_bhist accepted)
            (inscriptionRouteAuditDecode_encode_bhist downstream)
            (inscriptionRouteAuditDecode_encode_bhist transport)
            (inscriptionRouteAuditDecode_encode_bhist cont)
            (inscriptionRouteAuditDecode_encode_bhist provenance)
            (inscriptionRouteAuditDecode_encode_bhist name))

private theorem inscriptionRouteAuditToEventFlow_injective {x y : InscriptionRouteAuditUp} :
    inscriptionRouteAuditToEventFlow x = inscriptionRouteAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionRouteAuditFromEventFlow (inscriptionRouteAuditToEventFlow x) =
        inscriptionRouteAuditFromEventFlow (inscriptionRouteAuditToEventFlow y) :=
    congrArg inscriptionRouteAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionRouteAudit_round_trip x).symm
      (Eq.trans hread (inscriptionRouteAudit_round_trip y)))

private def inscriptionRouteAuditFields : InscriptionRouteAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionRouteAuditUp.mk source gap route accepted downstream transport cont provenance
      name =>
      [source, gap, route, accepted, downstream, transport, cont, provenance, name]

private theorem inscriptionRouteAudit_field_faithful :
    ∀ x y : InscriptionRouteAuditUp,
      inscriptionRouteAuditFields x = inscriptionRouteAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk source₁ gap₁ route₁ accepted₁ downstream₁ transport₁ cont₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ gap₂ route₂ accepted₂ downstream₂ transport₂ cont₂ provenance₂ name₂ =>
          cases h
          rfl

instance inscriptionRouteAuditBHistCarrier : BHistCarrier InscriptionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionRouteAuditToEventFlow
  fromEventFlow := inscriptionRouteAuditFromEventFlow

instance inscriptionRouteAuditChapterTasteGate : ChapterTasteGate InscriptionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscriptionRouteAuditFromEventFlow (inscriptionRouteAuditToEventFlow x) = some x
    exact inscriptionRouteAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionRouteAuditToEventFlow_injective heq)

instance inscriptionRouteAuditFieldFaithful : FieldFaithful InscriptionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionRouteAuditFields
  field_faithful := inscriptionRouteAudit_field_faithful

instance inscriptionRouteAuditNontrivial : Nontrivial InscriptionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InscriptionRouteAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionRouteAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionRouteAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inscriptionRouteAuditChapterTasteGate

theorem InscriptionRouteAuditTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate InscriptionRouteAuditUp) ∧
      Nonempty (FieldFaithful InscriptionRouteAuditUp) ∧
        Nonempty (Nontrivial InscriptionRouteAuditUp) ∧
          (∀ h : BHist,
            inscriptionRouteAuditDecodeBHist (inscriptionRouteAuditEncodeBHist h) = h) ∧
            (∀ x : InscriptionRouteAuditUp,
              inscriptionRouteAuditFromEventFlow (inscriptionRouteAuditToEventFlow x) =
                some x) ∧
              (∀ x y : InscriptionRouteAuditUp,
                inscriptionRouteAuditToEventFlow x = inscriptionRouteAuditToEventFlow y →
                  x = y) ∧
                inscriptionRouteAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact ⟨inscriptionRouteAuditChapterTasteGate⟩
  · constructor
    · exact ⟨inscriptionRouteAuditFieldFaithful⟩
    · constructor
      · exact ⟨inscriptionRouteAuditNontrivial⟩
      · constructor
        · exact inscriptionRouteAuditDecode_encode_bhist
        · constructor
          · exact inscriptionRouteAudit_round_trip
          · constructor
            · intro x y heq
              exact inscriptionRouteAuditToEventFlow_injective heq
            · rfl

end BEDC.Derived.InscriptionRouteAuditUp
