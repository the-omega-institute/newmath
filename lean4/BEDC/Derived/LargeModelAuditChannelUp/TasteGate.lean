import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelAuditChannelUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelAuditChannelUp : Type where
  | mk (prompt response activation audit replay transport provenance nameCert : BHist) :
      LargeModelAuditChannelUp
  deriving DecidableEq

private def largeModelAuditChannelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelAuditChannelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelAuditChannelEncodeBHist h

private def largeModelAuditChannelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelAuditChannelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelAuditChannelDecodeBHist tail)

private theorem largeModelAuditChannelDecode_encode_bhist :
    ∀ h : BHist,
      largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def largeModelAuditChannelToEventFlow : LargeModelAuditChannelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelAuditChannelUp.mk prompt response activation audit replay transport provenance
      nameCert =>
      [[BMark.b0],
        largeModelAuditChannelEncodeBHist prompt,
        [BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist response,
        [BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist activation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        largeModelAuditChannelEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        largeModelAuditChannelEncodeBHist nameCert]

private def largeModelAuditChannelFromEventFlow : EventFlow → Option LargeModelAuditChannelUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | prompt :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | response :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | activation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | audit :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
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
                                                                        (LargeModelAuditChannelUp.mk
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            prompt)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            response)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            activation)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            audit)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            replay)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            transport)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            provenance)
                                                                          (largeModelAuditChannelDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem largeModelAuditChannel_round_trip :
    ∀ x : LargeModelAuditChannelUp,
      largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk prompt response activation audit replay transport provenance nameCert =>
      change
        some
          (LargeModelAuditChannelUp.mk
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist prompt))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist response))
            (largeModelAuditChannelDecodeBHist
              (largeModelAuditChannelEncodeBHist activation))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist audit))
            (largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist replay))
            (largeModelAuditChannelDecodeBHist
              (largeModelAuditChannelEncodeBHist transport))
            (largeModelAuditChannelDecodeBHist
              (largeModelAuditChannelEncodeBHist provenance))
            (largeModelAuditChannelDecodeBHist
              (largeModelAuditChannelEncodeBHist nameCert))) =
          some
            (LargeModelAuditChannelUp.mk prompt response activation audit replay transport
              provenance nameCert)
      rw [largeModelAuditChannelDecode_encode_bhist prompt,
        largeModelAuditChannelDecode_encode_bhist response,
        largeModelAuditChannelDecode_encode_bhist activation,
        largeModelAuditChannelDecode_encode_bhist audit,
        largeModelAuditChannelDecode_encode_bhist replay,
        largeModelAuditChannelDecode_encode_bhist transport,
        largeModelAuditChannelDecode_encode_bhist provenance,
        largeModelAuditChannelDecode_encode_bhist nameCert]

private theorem largeModelAuditChannelToEventFlow_injective
    {x y : LargeModelAuditChannelUp} :
    largeModelAuditChannelToEventFlow x = largeModelAuditChannelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) =
        largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow y) :=
    congrArg largeModelAuditChannelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelAuditChannel_round_trip x).symm
      (Eq.trans hread (largeModelAuditChannel_round_trip y)))

instance largeModelAuditChannelBHistCarrier : BHistCarrier LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelAuditChannelToEventFlow
  fromEventFlow := largeModelAuditChannelFromEventFlow

instance largeModelAuditChannelChapterTasteGate :
    ChapterTasteGate LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x
    exact largeModelAuditChannel_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelAuditChannelToEventFlow_injective heq)

instance largeModelAuditChannelFieldFaithful : FieldFaithful LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LargeModelAuditChannelUp.mk prompt response activation audit replay transport
        provenance nameCert =>
        [prompt, response, activation, audit, replay, transport, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk prompt₁ response₁ activation₁ audit₁ replay₁ transport₁ provenance₁ nameCert₁ =>
        cases y with
        | mk prompt₂ response₂ activation₂ audit₂ replay₂ transport₂ provenance₂ nameCert₂ =>
            injection h with hprompt t1
            injection t1 with hresponse t2
            injection t2 with hactivation t3
            injection t3 with haudit t4
            injection t4 with hreplay t5
            injection t5 with htransport t6
            injection t6 with hprovenance t7
            injection t7 with hnameCert _
            cases hprompt
            cases hresponse
            cases hactivation
            cases haudit
            cases hreplay
            cases htransport
            cases hprovenance
            cases hnameCert
            rfl

instance largeModelAuditChannelNontrivial : Nontrivial LargeModelAuditChannelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LargeModelAuditChannelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelAuditChannelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LargeModelAuditChannelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  largeModelAuditChannelChapterTasteGate

theorem LargeModelAuditChannelTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      largeModelAuditChannelDecodeBHist (largeModelAuditChannelEncodeBHist h) = h) ∧
      (∀ x : LargeModelAuditChannelUp,
        largeModelAuditChannelFromEventFlow (largeModelAuditChannelToEventFlow x) = some x) ∧
        (∀ x y : LargeModelAuditChannelUp,
          largeModelAuditChannelToEventFlow x =
            largeModelAuditChannelToEventFlow y → x = y) ∧
          largeModelAuditChannelEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelAuditChannelDecode_encode_bhist
  · constructor
    · exact largeModelAuditChannel_round_trip
    · constructor
      · intro x y heq
        exact largeModelAuditChannelToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelAuditChannelUp
