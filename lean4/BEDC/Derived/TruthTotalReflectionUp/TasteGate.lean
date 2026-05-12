import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TruthTotalReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TruthTotalReflectionUp : Type where
  | mk :
      (sentences attempts diagonal transports routes provenance localName : BHist) →
        TruthTotalReflectionUp
  deriving DecidableEq

private def TruthTotalReflectionUp_taste_gate_boundary_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: TruthTotalReflectionUp_taste_gate_boundary_encodeBHist h
  | BHist.e1 h => BMark.b1 :: TruthTotalReflectionUp_taste_gate_boundary_encodeBHist h

private def TruthTotalReflectionUp_taste_gate_boundary_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist tail)

private theorem TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist :
    ∀ h : BHist,
      TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
        (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def TruthTotalReflectionUp_taste_gate_boundary_toEventFlow :
    TruthTotalReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TruthTotalReflectionUp.mk sentences attempts diagonal transports routes provenance localName =>
      [[BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist sentences,
        [BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist attempts,
        [BMark.b1, BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        TruthTotalReflectionUp_taste_gate_boundary_encodeBHist localName]

private def TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow :
    EventFlow → Option TruthTotalReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sentences :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | attempts :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagonal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transports :: rest7 =>
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
                                                      | localName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (TruthTotalReflectionUp.mk
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    sentences)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    attempts)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    diagonal)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    transports)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    routes)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    provenance)
                                                                  (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
                                                                    localName))
                                                          | _ :: _ => none

private theorem TruthTotalReflectionUp_taste_gate_boundary_round_trip :
    ∀ x : TruthTotalReflectionUp,
      TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow
        (TruthTotalReflectionUp_taste_gate_boundary_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sentences attempts diagonal transports routes provenance localName =>
      change
        some
          (TruthTotalReflectionUp.mk
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist sentences))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist attempts))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist diagonal))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist transports))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist routes))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist provenance))
            (TruthTotalReflectionUp_taste_gate_boundary_decodeBHist
              (TruthTotalReflectionUp_taste_gate_boundary_encodeBHist localName))) =
          some
            (TruthTotalReflectionUp.mk sentences attempts diagonal transports routes provenance
              localName)
      rw [TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist sentences,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist attempts,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist diagonal,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist transports,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist routes,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist provenance,
        TruthTotalReflectionUp_taste_gate_boundary_decode_encode_bhist localName]

private theorem TruthTotalReflectionUp_taste_gate_boundary_toEventFlow_injective
    {x y : TruthTotalReflectionUp} :
    TruthTotalReflectionUp_taste_gate_boundary_toEventFlow x =
      TruthTotalReflectionUp_taste_gate_boundary_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow
          (TruthTotalReflectionUp_taste_gate_boundary_toEventFlow x) =
        TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow
          (TruthTotalReflectionUp_taste_gate_boundary_toEventFlow y) :=
    congrArg TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TruthTotalReflectionUp_taste_gate_boundary_round_trip x).symm
      (Eq.trans hread (TruthTotalReflectionUp_taste_gate_boundary_round_trip y)))

instance truthTotalReflectionBHistCarrier : BHistCarrier TruthTotalReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := TruthTotalReflectionUp_taste_gate_boundary_toEventFlow
  fromEventFlow := TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow

instance truthTotalReflectionChapterTasteGate : ChapterTasteGate TruthTotalReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      TruthTotalReflectionUp_taste_gate_boundary_fromEventFlow
        (TruthTotalReflectionUp_taste_gate_boundary_toEventFlow x) = some x
    exact TruthTotalReflectionUp_taste_gate_boundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TruthTotalReflectionUp_taste_gate_boundary_toEventFlow_injective heq)

theorem TruthTotalReflectionUp_taste_gate_boundary :
    (∀ x : TruthTotalReflectionUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (x : TruthTotalReflectionUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact
      ⟨TruthTotalReflectionUp_taste_gate_boundary_toEventFlow x,
        TruthTotalReflectionUp_taste_gate_boundary_round_trip x⟩
  · intro x w m hw hm
    exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

end BEDC.Derived.TruthTotalReflectionUp
