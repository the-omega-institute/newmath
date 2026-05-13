import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuntimeReflectionBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuntimeReflectionBoundaryUp : Type where
  | mk :
      (selfDescription runtimeRequest executionRefusal boundaryReport transport routes
        provenance nameCert : BHist) →
      RuntimeReflectionBoundaryUp

def runtimeReflectionBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: runtimeReflectionBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: runtimeReflectionBoundaryEncodeBHist h

def runtimeReflectionBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (runtimeReflectionBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (runtimeReflectionBoundaryDecodeBHist tail)

private theorem runtimeReflectionBoundary_decode_encode_bhist :
    ∀ h : BHist,
      runtimeReflectionBoundaryDecodeBHist (runtimeReflectionBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def runtimeReflectionBoundaryToEventFlow : RuntimeReflectionBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RuntimeReflectionBoundaryUp.mk selfDescription runtimeRequest executionRefusal boundaryReport
      transport routes provenance nameCert =>
      [[BMark.b0],
        runtimeReflectionBoundaryEncodeBHist selfDescription,
        [BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist runtimeRequest,
        [BMark.b1, BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist executionRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist boundaryReport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeReflectionBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        runtimeReflectionBoundaryEncodeBHist nameCert]

private def runtimeReflectionBoundaryDecodePacket
    (selfDescription runtimeRequest executionRefusal boundaryReport transport routes provenance
      nameCert : RawEvent) : RuntimeReflectionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RuntimeReflectionBoundaryUp.mk
    (runtimeReflectionBoundaryDecodeBHist selfDescription)
    (runtimeReflectionBoundaryDecodeBHist runtimeRequest)
    (runtimeReflectionBoundaryDecodeBHist executionRefusal)
    (runtimeReflectionBoundaryDecodeBHist boundaryReport)
    (runtimeReflectionBoundaryDecodeBHist transport)
    (runtimeReflectionBoundaryDecodeBHist routes)
    (runtimeReflectionBoundaryDecodeBHist provenance)
    (runtimeReflectionBoundaryDecodeBHist nameCert)

def runtimeReflectionBoundaryFromEventFlow :
    EventFlow → Option RuntimeReflectionBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selfDescription :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | runtimeRequest :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | executionRefusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundaryReport :: rest7 =>
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
                                              | routes :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (runtimeReflectionBoundaryDecodePacket
                                                                          selfDescription
                                                                          runtimeRequest
                                                                          executionRefusal
                                                                          boundaryReport
                                                                          transport
                                                                          routes
                                                                          provenance
                                                                          nameCert)
                                                                  | _ :: _ => none

private theorem runtimeReflectionBoundaryMkCongr
    {selfDescription selfDescription' runtimeRequest runtimeRequest' executionRefusal
      executionRefusal' boundaryReport boundaryReport' transport transport' routes routes'
      provenance provenance' nameCert nameCert' : BHist}
    (hSelfDescription : selfDescription' = selfDescription)
    (hRuntimeRequest : runtimeRequest' = runtimeRequest)
    (hExecutionRefusal : executionRefusal' = executionRefusal)
    (hBoundaryReport : boundaryReport' = boundaryReport)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    RuntimeReflectionBoundaryUp.mk selfDescription' runtimeRequest' executionRefusal'
        boundaryReport' transport' routes' provenance' nameCert' =
      RuntimeReflectionBoundaryUp.mk selfDescription runtimeRequest executionRefusal
        boundaryReport transport routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSelfDescription
  cases hRuntimeRequest
  cases hExecutionRefusal
  cases hBoundaryReport
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private theorem runtimeReflectionBoundary_round_trip :
    ∀ x : RuntimeReflectionBoundaryUp,
      runtimeReflectionBoundaryFromEventFlow (runtimeReflectionBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selfDescription runtimeRequest executionRefusal boundaryReport transport routes
      provenance nameCert =>
      change
        some
          (runtimeReflectionBoundaryDecodePacket
            (runtimeReflectionBoundaryEncodeBHist selfDescription)
            (runtimeReflectionBoundaryEncodeBHist runtimeRequest)
            (runtimeReflectionBoundaryEncodeBHist executionRefusal)
            (runtimeReflectionBoundaryEncodeBHist boundaryReport)
            (runtimeReflectionBoundaryEncodeBHist transport)
            (runtimeReflectionBoundaryEncodeBHist routes)
            (runtimeReflectionBoundaryEncodeBHist provenance)
            (runtimeReflectionBoundaryEncodeBHist nameCert)) =
          some
            (RuntimeReflectionBoundaryUp.mk selfDescription runtimeRequest executionRefusal
              boundaryReport transport routes provenance nameCert)
      unfold runtimeReflectionBoundaryDecodePacket
      exact
        congrArg some
          (runtimeReflectionBoundaryMkCongr
            (runtimeReflectionBoundary_decode_encode_bhist selfDescription)
            (runtimeReflectionBoundary_decode_encode_bhist runtimeRequest)
            (runtimeReflectionBoundary_decode_encode_bhist executionRefusal)
            (runtimeReflectionBoundary_decode_encode_bhist boundaryReport)
            (runtimeReflectionBoundary_decode_encode_bhist transport)
            (runtimeReflectionBoundary_decode_encode_bhist routes)
            (runtimeReflectionBoundary_decode_encode_bhist provenance)
            (runtimeReflectionBoundary_decode_encode_bhist nameCert))

private theorem runtimeReflectionBoundaryToEventFlow_injective
    {x y : RuntimeReflectionBoundaryUp} :
    runtimeReflectionBoundaryToEventFlow x =
      runtimeReflectionBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      runtimeReflectionBoundaryFromEventFlow (runtimeReflectionBoundaryToEventFlow x) =
        runtimeReflectionBoundaryFromEventFlow (runtimeReflectionBoundaryToEventFlow y) :=
    congrArg runtimeReflectionBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (runtimeReflectionBoundary_round_trip x).symm
      (Eq.trans hread (runtimeReflectionBoundary_round_trip y)))

private def runtimeReflectionBoundaryFields :
    RuntimeReflectionBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuntimeReflectionBoundaryUp.mk selfDescription runtimeRequest executionRefusal boundaryReport
      transport routes provenance nameCert =>
      [selfDescription, runtimeRequest, executionRefusal, boundaryReport, transport, routes,
        provenance, nameCert]

private theorem runtimeReflectionBoundary_field_faithful :
    ∀ x y : RuntimeReflectionBoundaryUp,
      runtimeReflectionBoundaryFields x = runtimeReflectionBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk selfDescription runtimeRequest executionRefusal boundaryReport transport routes
      provenance nameCert =>
      cases y with
      | mk selfDescription' runtimeRequest' executionRefusal' boundaryReport' transport' routes'
          provenance' nameCert' =>
          cases hfields
          rfl

instance runtimeReflectionBoundaryBHistCarrier :
    BHistCarrier RuntimeReflectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := runtimeReflectionBoundaryToEventFlow
  fromEventFlow := runtimeReflectionBoundaryFromEventFlow

instance runtimeReflectionBoundaryChapterTasteGate :
    ChapterTasteGate RuntimeReflectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      runtimeReflectionBoundaryFromEventFlow
        (runtimeReflectionBoundaryToEventFlow x) = some x
    exact runtimeReflectionBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (runtimeReflectionBoundaryToEventFlow_injective heq)

instance runtimeReflectionBoundaryFieldFaithful :
    FieldFaithful RuntimeReflectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := runtimeReflectionBoundaryFields
  field_faithful := runtimeReflectionBoundary_field_faithful

instance runtimeReflectionBoundaryNontrivial :
    Nontrivial RuntimeReflectionBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RuntimeReflectionBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RuntimeReflectionBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RuntimeReflectionBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  runtimeReflectionBoundaryChapterTasteGate

theorem RuntimeReflectionBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RuntimeReflectionBoundaryUp) ∧
      Nonempty (FieldFaithful RuntimeReflectionBoundaryUp) ∧
      Nonempty (Nontrivial RuntimeReflectionBoundaryUp) ∧
        (∀ h : BHist,
          runtimeReflectionBoundaryDecodeBHist (runtimeReflectionBoundaryEncodeBHist h) = h) ∧
          runtimeReflectionBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨runtimeReflectionBoundaryChapterTasteGate⟩, ⟨runtimeReflectionBoundaryFieldFaithful⟩,
      ⟨runtimeReflectionBoundaryNontrivial⟩, runtimeReflectionBoundary_decode_encode_bhist, rfl⟩

end BEDC.Derived.RuntimeReflectionBoundaryUp
