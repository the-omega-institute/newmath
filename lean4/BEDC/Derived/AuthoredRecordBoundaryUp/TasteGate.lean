import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuthoredRecordBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuthoredRecordBoundaryUp : Type where
  | mk :
      (observer schedule mismatch acceptedRoute publicRecord refusal transport routeReplay
        provenance handoff consumer packageRow nameCert : BHist) →
      AuthoredRecordBoundaryUp

def authoredRecordBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: authoredRecordBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: authoredRecordBoundaryEncodeBHist h

def authoredRecordBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (authoredRecordBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (authoredRecordBoundaryDecodeBHist tail)

private theorem authoredRecordBoundary_decode_encode_bhist :
    ∀ h : BHist,
      authoredRecordBoundaryDecodeBHist (authoredRecordBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def authoredRecordBoundaryToEventFlow : AuthoredRecordBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuthoredRecordBoundaryUp.mk observer schedule mismatch acceptedRoute publicRecord refusal
      transport routeReplay provenance handoff consumer packageRow nameCert =>
      [authoredRecordBoundaryEncodeBHist observer,
        authoredRecordBoundaryEncodeBHist schedule,
        authoredRecordBoundaryEncodeBHist mismatch,
        authoredRecordBoundaryEncodeBHist acceptedRoute,
        authoredRecordBoundaryEncodeBHist publicRecord,
        authoredRecordBoundaryEncodeBHist refusal,
        authoredRecordBoundaryEncodeBHist transport,
        authoredRecordBoundaryEncodeBHist routeReplay,
        authoredRecordBoundaryEncodeBHist provenance,
        authoredRecordBoundaryEncodeBHist handoff,
        authoredRecordBoundaryEncodeBHist consumer,
        authoredRecordBoundaryEncodeBHist packageRow,
        authoredRecordBoundaryEncodeBHist nameCert]

private def authoredRecordBoundaryDecodePacket
    (observer schedule mismatch acceptedRoute publicRecord refusal transport routeReplay
      provenance handoff consumer packageRow nameCert : RawEvent) : AuthoredRecordBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  AuthoredRecordBoundaryUp.mk
    (authoredRecordBoundaryDecodeBHist observer)
    (authoredRecordBoundaryDecodeBHist schedule)
    (authoredRecordBoundaryDecodeBHist mismatch)
    (authoredRecordBoundaryDecodeBHist acceptedRoute)
    (authoredRecordBoundaryDecodeBHist publicRecord)
    (authoredRecordBoundaryDecodeBHist refusal)
    (authoredRecordBoundaryDecodeBHist transport)
    (authoredRecordBoundaryDecodeBHist routeReplay)
    (authoredRecordBoundaryDecodeBHist provenance)
    (authoredRecordBoundaryDecodeBHist handoff)
    (authoredRecordBoundaryDecodeBHist consumer)
    (authoredRecordBoundaryDecodeBHist packageRow)
    (authoredRecordBoundaryDecodeBHist nameCert)

def authoredRecordBoundaryFromEventFlow : EventFlow → Option AuthoredRecordBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | observer :: rest0 =>
      match rest0 with
      | [] => none
      | schedule :: rest1 =>
          match rest1 with
          | [] => none
          | mismatch :: rest2 =>
              match rest2 with
              | [] => none
              | acceptedRoute :: rest3 =>
                  match rest3 with
                  | [] => none
                  | publicRecord :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routeReplay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | handoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | consumer :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | packageRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | nameCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (authoredRecordBoundaryDecodePacket
                                                              observer schedule mismatch
                                                              acceptedRoute publicRecord refusal
                                                              transport routeReplay provenance
                                                              handoff consumer packageRow
                                                              nameCert)
                                                      | _ :: _ => none

private theorem authoredRecordBoundary_round_trip :
    ∀ x : AuthoredRecordBoundaryUp,
      authoredRecordBoundaryFromEventFlow (authoredRecordBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer schedule mismatch acceptedRoute publicRecord refusal transport routeReplay
      provenance handoff consumer packageRow nameCert =>
      change
        some
          (authoredRecordBoundaryDecodePacket
            (authoredRecordBoundaryEncodeBHist observer)
            (authoredRecordBoundaryEncodeBHist schedule)
            (authoredRecordBoundaryEncodeBHist mismatch)
            (authoredRecordBoundaryEncodeBHist acceptedRoute)
            (authoredRecordBoundaryEncodeBHist publicRecord)
            (authoredRecordBoundaryEncodeBHist refusal)
            (authoredRecordBoundaryEncodeBHist transport)
            (authoredRecordBoundaryEncodeBHist routeReplay)
            (authoredRecordBoundaryEncodeBHist provenance)
            (authoredRecordBoundaryEncodeBHist handoff)
            (authoredRecordBoundaryEncodeBHist consumer)
            (authoredRecordBoundaryEncodeBHist packageRow)
            (authoredRecordBoundaryEncodeBHist nameCert)) =
          some
            (AuthoredRecordBoundaryUp.mk observer schedule mismatch acceptedRoute publicRecord
              refusal transport routeReplay provenance handoff consumer packageRow nameCert)
      unfold authoredRecordBoundaryDecodePacket
      rw [authoredRecordBoundary_decode_encode_bhist observer,
        authoredRecordBoundary_decode_encode_bhist schedule,
        authoredRecordBoundary_decode_encode_bhist mismatch,
        authoredRecordBoundary_decode_encode_bhist acceptedRoute,
        authoredRecordBoundary_decode_encode_bhist publicRecord,
        authoredRecordBoundary_decode_encode_bhist refusal,
        authoredRecordBoundary_decode_encode_bhist transport,
        authoredRecordBoundary_decode_encode_bhist routeReplay,
        authoredRecordBoundary_decode_encode_bhist provenance,
        authoredRecordBoundary_decode_encode_bhist handoff,
        authoredRecordBoundary_decode_encode_bhist consumer,
        authoredRecordBoundary_decode_encode_bhist packageRow,
        authoredRecordBoundary_decode_encode_bhist nameCert]

private theorem authoredRecordBoundaryToEventFlow_injective
    {x y : AuthoredRecordBoundaryUp} :
    authoredRecordBoundaryToEventFlow x = authoredRecordBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      authoredRecordBoundaryFromEventFlow (authoredRecordBoundaryToEventFlow x) =
        authoredRecordBoundaryFromEventFlow (authoredRecordBoundaryToEventFlow y) :=
    congrArg authoredRecordBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (authoredRecordBoundary_round_trip x).symm
      (Eq.trans hread (authoredRecordBoundary_round_trip y)))

private def authoredRecordBoundaryFields :
    AuthoredRecordBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuthoredRecordBoundaryUp.mk observer schedule mismatch acceptedRoute publicRecord refusal
      transport routeReplay provenance handoff consumer packageRow nameCert =>
      [observer, schedule, mismatch, acceptedRoute, publicRecord, refusal, transport,
        routeReplay, provenance, handoff, consumer, packageRow, nameCert]

private theorem authoredRecordBoundary_field_faithful :
    ∀ x y : AuthoredRecordBoundaryUp,
      authoredRecordBoundaryFields x = authoredRecordBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observer schedule mismatch acceptedRoute publicRecord refusal transport routeReplay
      provenance handoff consumer packageRow nameCert =>
      cases y with
      | mk observer' schedule' mismatch' acceptedRoute' publicRecord' refusal' transport'
          routeReplay' provenance' handoff' consumer' packageRow' nameCert' =>
          cases hfields
          rfl

instance authoredRecordBoundaryBHistCarrier : BHistCarrier AuthoredRecordBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := authoredRecordBoundaryToEventFlow
  fromEventFlow := authoredRecordBoundaryFromEventFlow

instance authoredRecordBoundaryChapterTasteGate :
    ChapterTasteGate AuthoredRecordBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change authoredRecordBoundaryFromEventFlow (authoredRecordBoundaryToEventFlow x) = some x
    exact authoredRecordBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (authoredRecordBoundaryToEventFlow_injective heq)

instance authoredRecordBoundaryFieldFaithful :
    FieldFaithful AuthoredRecordBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := authoredRecordBoundaryFields
  field_faithful := authoredRecordBoundary_field_faithful

instance authoredRecordBoundaryNontrivial : Nontrivial AuthoredRecordBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuthoredRecordBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AuthoredRecordBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuthoredRecordBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  authoredRecordBoundaryChapterTasteGate

theorem AuthoredRecordBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      authoredRecordBoundaryDecodeBHist (authoredRecordBoundaryEncodeBHist h) = h) ∧
      (∀ x : AuthoredRecordBoundaryUp,
        authoredRecordBoundaryFromEventFlow (authoredRecordBoundaryToEventFlow x) = some x) ∧
      (∀ x y : AuthoredRecordBoundaryUp,
        authoredRecordBoundaryToEventFlow x = authoredRecordBoundaryToEventFlow y → x = y) ∧
      authoredRecordBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨authoredRecordBoundary_decode_encode_bhist, authoredRecordBoundary_round_trip,
      (fun _ _ heq => authoredRecordBoundaryToEventFlow_injective heq), rfl⟩

end BEDC.Derived.AuthoredRecordBoundaryUp
