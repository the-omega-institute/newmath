import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCarrierNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCarrierNameCertUp : Type where
  | mk :
      (A B WA WB DA DB S Delta V T Q R E H C P N : BHist) ->
      CauchyCarrierNameCertUp
  deriving DecidableEq

def cauchyCarrierNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCarrierNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCarrierNameCertEncodeBHist h

def cauchyCarrierNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCarrierNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCarrierNameCertDecodeBHist tail)

private theorem cauchyCarrierNameCert_decode_encode_bhist :
    forall h : BHist,
      cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCarrierNameCertFields : CauchyCarrierNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCarrierNameCertUp.mk A B WA WB DA DB S Delta V T Q R E H C P N =>
      [A, B, WA, WB, DA, DB, S, Delta, V, T, Q, R, E, H, C, P, N]

def cauchyCarrierNameCertToEventFlow : CauchyCarrierNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCarrierNameCertFields x).map cauchyCarrierNameCertEncodeBHist

def cauchyCarrierNameCertFromEventFlow : EventFlow -> Option CauchyCarrierNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: restA =>
      match restA with
      | B :: restB =>
          match restB with
          | WA :: restWA =>
              match restWA with
              | WB :: restWB =>
                  match restWB with
                  | DA :: restDA =>
                      match restDA with
                      | DB :: restDB =>
                          match restDB with
                          | S :: restS =>
                              match restS with
                              | Delta :: restDelta =>
                                  match restDelta with
                                  | V :: restV =>
                                      match restV with
                                      | T :: restT =>
                                          match restT with
                                          | Q :: restQ =>
                                              match restQ with
                                              | R :: restR =>
                                                  match restR with
                                                  | E :: restE =>
                                                      match restE with
                                                      | H :: restH =>
                                                          match restH with
                                                          | C :: restC =>
                                                              match restC with
                                                              | P :: restP =>
                                                                  match restP with
                                                                  | N :: restN =>
                                                                      match restN with
                                                                      | [] =>
                                                                          some
                                                                            (CauchyCarrierNameCertUp.mk
                                                                              (cauchyCarrierNameCertDecodeBHist A)
                                                                              (cauchyCarrierNameCertDecodeBHist B)
                                                                              (cauchyCarrierNameCertDecodeBHist WA)
                                                                              (cauchyCarrierNameCertDecodeBHist WB)
                                                                              (cauchyCarrierNameCertDecodeBHist DA)
                                                                              (cauchyCarrierNameCertDecodeBHist DB)
                                                                              (cauchyCarrierNameCertDecodeBHist S)
                                                                              (cauchyCarrierNameCertDecodeBHist Delta)
                                                                              (cauchyCarrierNameCertDecodeBHist V)
                                                                              (cauchyCarrierNameCertDecodeBHist T)
                                                                              (cauchyCarrierNameCertDecodeBHist Q)
                                                                              (cauchyCarrierNameCertDecodeBHist R)
                                                                              (cauchyCarrierNameCertDecodeBHist E)
                                                                              (cauchyCarrierNameCertDecodeBHist H)
                                                                              (cauchyCarrierNameCertDecodeBHist C)
                                                                              (cauchyCarrierNameCertDecodeBHist P)
                                                                              (cauchyCarrierNameCertDecodeBHist N))
                                                                      | _ :: _ => none
                                                                  | [] => none
                                                              | [] => none
                                                          | [] => none
                                                      | [] => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyCarrierNameCert_round_trip :
    forall x : CauchyCarrierNameCertUp,
      cauchyCarrierNameCertFromEventFlow (cauchyCarrierNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB DA DB S Delta V T Q R E H C P N =>
      change
        some
          (CauchyCarrierNameCertUp.mk
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist A))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist B))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist WA))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist WB))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist DA))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist DB))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist S))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist Delta))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist V))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist T))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist Q))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist R))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist E))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist H))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist C))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist P))
            (cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist N))) =
          some (CauchyCarrierNameCertUp.mk A B WA WB DA DB S Delta V T Q R E H C P N)
      rw [cauchyCarrierNameCert_decode_encode_bhist A,
        cauchyCarrierNameCert_decode_encode_bhist B,
        cauchyCarrierNameCert_decode_encode_bhist WA,
        cauchyCarrierNameCert_decode_encode_bhist WB,
        cauchyCarrierNameCert_decode_encode_bhist DA,
        cauchyCarrierNameCert_decode_encode_bhist DB,
        cauchyCarrierNameCert_decode_encode_bhist S,
        cauchyCarrierNameCert_decode_encode_bhist Delta,
        cauchyCarrierNameCert_decode_encode_bhist V,
        cauchyCarrierNameCert_decode_encode_bhist T,
        cauchyCarrierNameCert_decode_encode_bhist Q,
        cauchyCarrierNameCert_decode_encode_bhist R,
        cauchyCarrierNameCert_decode_encode_bhist E,
        cauchyCarrierNameCert_decode_encode_bhist H,
        cauchyCarrierNameCert_decode_encode_bhist C,
        cauchyCarrierNameCert_decode_encode_bhist P,
        cauchyCarrierNameCert_decode_encode_bhist N]

private theorem cauchyCarrierNameCertToEventFlow_injective
    {x y : CauchyCarrierNameCertUp} :
    cauchyCarrierNameCertToEventFlow x = cauchyCarrierNameCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCarrierNameCertFromEventFlow (cauchyCarrierNameCertToEventFlow x) =
        cauchyCarrierNameCertFromEventFlow (cauchyCarrierNameCertToEventFlow y) :=
    congrArg cauchyCarrierNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCarrierNameCert_round_trip x).symm
      (Eq.trans hread (cauchyCarrierNameCert_round_trip y)))

private theorem cauchyCarrierNameCert_field_faithful :
    forall x y : CauchyCarrierNameCertUp,
      cauchyCarrierNameCertFields x = cauchyCarrierNameCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A B WA WB DA DB S Delta V T Q R E H C P N =>
      cases y with
      | mk A' B' WA' WB' DA' DB' S' Delta' V' T' Q' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyCarrierNameCertBHistCarrier : BHistCarrier CauchyCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCarrierNameCertToEventFlow
  fromEventFlow := cauchyCarrierNameCertFromEventFlow

instance cauchyCarrierNameCertChapterTasteGate :
    ChapterTasteGate CauchyCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCarrierNameCertFromEventFlow (cauchyCarrierNameCertToEventFlow x) = some x
    exact cauchyCarrierNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCarrierNameCertToEventFlow_injective heq)

instance cauchyCarrierNameCertFieldFaithful : FieldFaithful CauchyCarrierNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCarrierNameCertFields
  field_faithful := cauchyCarrierNameCert_field_faithful

def taste_gate : ChapterTasteGate CauchyCarrierNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCarrierNameCertChapterTasteGate

theorem CauchyCarrierNameCertTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCarrierNameCertDecodeBHist (cauchyCarrierNameCertEncodeBHist h) = h) ∧
      (forall x : CauchyCarrierNameCertUp,
        cauchyCarrierNameCertFromEventFlow (cauchyCarrierNameCertToEventFlow x) =
          some x) ∧
        (forall x y : CauchyCarrierNameCertUp,
          cauchyCarrierNameCertToEventFlow x = cauchyCarrierNameCertToEventFlow y ->
            x = y) ∧
          cauchyCarrierNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyCarrierNameCert_decode_encode_bhist, cauchyCarrierNameCert_round_trip,
      (fun _ _ heq => cauchyCarrierNameCertToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CauchyCarrierNameCertUp
