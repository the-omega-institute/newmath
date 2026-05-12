import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecidableRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecidableRefutationUp : Type where
  | mk :
      (proposition refutation decision exclusions transports routes provenance localName :
        BHist) → DecidableRefutationUp
  deriving DecidableEq

private def DecidableRefutationUp_taste_gate_boundary_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DecidableRefutationUp_taste_gate_boundary_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DecidableRefutationUp_taste_gate_boundary_encodeBHist h

private def DecidableRefutationUp_taste_gate_boundary_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (DecidableRefutationUp_taste_gate_boundary_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (DecidableRefutationUp_taste_gate_boundary_decodeBHist tail)

private theorem DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist :
    ∀ h : BHist,
      DecidableRefutationUp_taste_gate_boundary_decodeBHist
        (DecidableRefutationUp_taste_gate_boundary_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def DecidableRefutationUp_taste_gate_boundary_toEventFlow :
    DecidableRefutationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DecidableRefutationUp.mk proposition refutation decision exclusions transports routes
      provenance localName =>
      [[BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist proposition,
        [BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist refutation,
        [BMark.b1, BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist exclusions,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        DecidableRefutationUp_taste_gate_boundary_encodeBHist localName]

private def DecidableRefutationUp_taste_gate_boundary_fromEventFlow :
    EventFlow → Option DecidableRefutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | proposition :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refutation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | decision :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exclusions :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transports :: rest9 =>
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
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DecidableRefutationUp.mk
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            proposition)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            refutation)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            decision)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            exclusions)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            transports)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            routes)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            provenance)
                                                                          (DecidableRefutationUp_taste_gate_boundary_decodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem DecidableRefutationUp_taste_gate_boundary_round_trip :
    ∀ x : DecidableRefutationUp,
      DecidableRefutationUp_taste_gate_boundary_fromEventFlow
        (DecidableRefutationUp_taste_gate_boundary_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk proposition refutation decision exclusions transports routes provenance localName =>
      change
        some
          (DecidableRefutationUp.mk
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist proposition))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist refutation))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist decision))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist exclusions))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist transports))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist routes))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist provenance))
            (DecidableRefutationUp_taste_gate_boundary_decodeBHist
              (DecidableRefutationUp_taste_gate_boundary_encodeBHist localName))) =
          some
            (DecidableRefutationUp.mk proposition refutation decision exclusions transports
              routes provenance localName)
      rw [DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist proposition,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist refutation,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist decision,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist exclusions,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist transports,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist routes,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist provenance,
        DecidableRefutationUp_taste_gate_boundary_decode_encode_bhist localName]

private theorem DecidableRefutationUp_taste_gate_boundary_toEventFlow_injective
    {x y : DecidableRefutationUp} :
    DecidableRefutationUp_taste_gate_boundary_toEventFlow x =
      DecidableRefutationUp_taste_gate_boundary_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DecidableRefutationUp_taste_gate_boundary_fromEventFlow
          (DecidableRefutationUp_taste_gate_boundary_toEventFlow x) =
        DecidableRefutationUp_taste_gate_boundary_fromEventFlow
          (DecidableRefutationUp_taste_gate_boundary_toEventFlow y) :=
    congrArg DecidableRefutationUp_taste_gate_boundary_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DecidableRefutationUp_taste_gate_boundary_round_trip x).symm
      (Eq.trans hread (DecidableRefutationUp_taste_gate_boundary_round_trip y)))

instance decidableRefutationBHistCarrier : BHistCarrier DecidableRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DecidableRefutationUp_taste_gate_boundary_toEventFlow
  fromEventFlow := DecidableRefutationUp_taste_gate_boundary_fromEventFlow

instance decidableRefutationChapterTasteGate : ChapterTasteGate DecidableRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DecidableRefutationUp_taste_gate_boundary_fromEventFlow
        (DecidableRefutationUp_taste_gate_boundary_toEventFlow x) = some x
    exact DecidableRefutationUp_taste_gate_boundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecidableRefutationUp_taste_gate_boundary_toEventFlow_injective heq)

theorem DecidableRefutationUp_taste_gate_boundary :
    ChapterTasteGate DecidableRefutationUp ∧
      (∀ (x : DecidableRefutationUp) (w : RawEvent) (m : DisplayAlphabet),
        List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decidableRefutationChapterTasteGate
  · intro x w m hw hm
    exact ChapterTasteGate.conservativity x w m hw hm

end BEDC.Derived.DecidableRefutationUp
