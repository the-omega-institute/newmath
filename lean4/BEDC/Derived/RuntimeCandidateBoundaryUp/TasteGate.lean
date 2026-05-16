import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RuntimeCandidateBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RuntimeCandidateBoundaryUp : Type where
  | mk :
      (source transition accepted transport routes provenance nameCert : BHist) →
      RuntimeCandidateBoundaryUp

def runtimeCandidateBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: runtimeCandidateBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: runtimeCandidateBoundaryEncodeBHist h

def runtimeCandidateBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (runtimeCandidateBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (runtimeCandidateBoundaryDecodeBHist tail)

private theorem runtimeCandidateBoundary_decode_encode_bhist :
    ∀ h : BHist,
      runtimeCandidateBoundaryDecodeBHist (runtimeCandidateBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def runtimeCandidateBoundaryToEventFlow : RuntimeCandidateBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RuntimeCandidateBoundaryUp.mk source transition accepted transport routes provenance nameCert =>
      [[BMark.b0],
        runtimeCandidateBoundaryEncodeBHist source,
        [BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist transition,
        [BMark.b1, BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist accepted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        runtimeCandidateBoundaryEncodeBHist nameCert]

private def runtimeCandidateBoundaryDecodePacket
    (source transition accepted transport routes provenance nameCert : RawEvent) :
    RuntimeCandidateBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RuntimeCandidateBoundaryUp.mk
    (runtimeCandidateBoundaryDecodeBHist source)
    (runtimeCandidateBoundaryDecodeBHist transition)
    (runtimeCandidateBoundaryDecodeBHist accepted)
    (runtimeCandidateBoundaryDecodeBHist transport)
    (runtimeCandidateBoundaryDecodeBHist routes)
    (runtimeCandidateBoundaryDecodeBHist provenance)
    (runtimeCandidateBoundaryDecodeBHist nameCert)

def runtimeCandidateBoundaryFromEventFlow :
    EventFlow → Option RuntimeCandidateBoundaryUp
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
              | transition :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | accepted :: rest5 =>
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
                                      | routes :: rest9 =>
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
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (runtimeCandidateBoundaryDecodePacket
                                                                  source transition accepted
                                                                  transport routes provenance
                                                                  nameCert)
                                                          | _ :: _ => none

private theorem runtimeCandidateBoundaryMkCongr
    {source source' transition transition' accepted accepted' transport transport'
      routes routes' provenance provenance' nameCert nameCert' : BHist}
    (hSource : source' = source)
    (hTransition : transition' = transition)
    (hAccepted : accepted' = accepted)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    RuntimeCandidateBoundaryUp.mk source' transition' accepted' transport' routes' provenance'
        nameCert' =
      RuntimeCandidateBoundaryUp.mk source transition accepted transport routes provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTransition
  cases hAccepted
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private theorem runtimeCandidateBoundary_round_trip :
    ∀ x : RuntimeCandidateBoundaryUp,
      runtimeCandidateBoundaryFromEventFlow (runtimeCandidateBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source transition accepted transport routes provenance nameCert =>
      change
        some
          (runtimeCandidateBoundaryDecodePacket
            (runtimeCandidateBoundaryEncodeBHist source)
            (runtimeCandidateBoundaryEncodeBHist transition)
            (runtimeCandidateBoundaryEncodeBHist accepted)
            (runtimeCandidateBoundaryEncodeBHist transport)
            (runtimeCandidateBoundaryEncodeBHist routes)
            (runtimeCandidateBoundaryEncodeBHist provenance)
            (runtimeCandidateBoundaryEncodeBHist nameCert)) =
          some
            (RuntimeCandidateBoundaryUp.mk source transition accepted transport routes provenance
              nameCert)
      unfold runtimeCandidateBoundaryDecodePacket
      exact
        congrArg some
          (runtimeCandidateBoundaryMkCongr
            (runtimeCandidateBoundary_decode_encode_bhist source)
            (runtimeCandidateBoundary_decode_encode_bhist transition)
            (runtimeCandidateBoundary_decode_encode_bhist accepted)
            (runtimeCandidateBoundary_decode_encode_bhist transport)
            (runtimeCandidateBoundary_decode_encode_bhist routes)
            (runtimeCandidateBoundary_decode_encode_bhist provenance)
            (runtimeCandidateBoundary_decode_encode_bhist nameCert))

private theorem runtimeCandidateBoundaryToEventFlow_injective
    {x y : RuntimeCandidateBoundaryUp} :
    runtimeCandidateBoundaryToEventFlow x = runtimeCandidateBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      runtimeCandidateBoundaryFromEventFlow (runtimeCandidateBoundaryToEventFlow x) =
        runtimeCandidateBoundaryFromEventFlow (runtimeCandidateBoundaryToEventFlow y) :=
    congrArg runtimeCandidateBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (runtimeCandidateBoundary_round_trip x).symm
      (Eq.trans hread (runtimeCandidateBoundary_round_trip y)))

private def runtimeCandidateBoundaryFields :
    RuntimeCandidateBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RuntimeCandidateBoundaryUp.mk source transition accepted transport routes provenance nameCert =>
      [source, transition, accepted, transport, routes, provenance, nameCert]

private theorem runtimeCandidateBoundary_field_faithful :
    ∀ x y : RuntimeCandidateBoundaryUp,
      runtimeCandidateBoundaryFields x = runtimeCandidateBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source transition accepted transport routes provenance nameCert =>
      cases y with
      | mk source' transition' accepted' transport' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance runtimeCandidateBoundaryBHistCarrier :
    BHistCarrier RuntimeCandidateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := runtimeCandidateBoundaryToEventFlow
  fromEventFlow := runtimeCandidateBoundaryFromEventFlow

instance runtimeCandidateBoundaryChapterTasteGate :
    ChapterTasteGate RuntimeCandidateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      runtimeCandidateBoundaryFromEventFlow (runtimeCandidateBoundaryToEventFlow x) = some x
    exact runtimeCandidateBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (runtimeCandidateBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RuntimeCandidateBoundaryUp :=
  runtimeCandidateBoundaryChapterTasteGate

instance runtimeCandidateBoundaryFieldFaithful :
    FieldFaithful RuntimeCandidateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := runtimeCandidateBoundaryFields
  field_faithful := runtimeCandidateBoundary_field_faithful

theorem RuntimeCandidateBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, runtimeCandidateBoundaryDecodeBHist (runtimeCandidateBoundaryEncodeBHist h) = h) ∧
      (∀ x : RuntimeCandidateBoundaryUp,
        runtimeCandidateBoundaryFromEventFlow (runtimeCandidateBoundaryToEventFlow x) = some x) ∧
      (∀ x y : RuntimeCandidateBoundaryUp,
        runtimeCandidateBoundaryToEventFlow x = runtimeCandidateBoundaryToEventFlow y -> x = y) ∧
      runtimeCandidateBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨runtimeCandidateBoundary_decode_encode_bhist, runtimeCandidateBoundary_round_trip,
      fun _ _ heq => runtimeCandidateBoundaryToEventFlow_injective heq, rfl⟩

end BEDC.Derived.RuntimeCandidateBoundaryUp
