import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AttentionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AttentionLedgerUp : Type where
  | mk :
      (source filter selected omitted publicRow stream transport exactness routes provenance
        nameCert : BHist) →
      AttentionLedgerUp

def attentionLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: attentionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: attentionLedgerEncodeBHist h

def attentionLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (attentionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (attentionLedgerDecodeBHist tail)

private theorem attentionLedgerDecode_encode_bhist :
    ∀ h : BHist, attentionLedgerDecodeBHist (attentionLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def attentionLedgerToEventFlow : AttentionLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AttentionLedgerUp.mk source filter selected omitted publicRow stream transport exactness
      routes provenance nameCert =>
      [[BMark.b0],
        attentionLedgerEncodeBHist source,
        [BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist filter,
        [BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist selected,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist omitted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist publicRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        attentionLedgerEncodeBHist exactness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        attentionLedgerEncodeBHist nameCert]

def attentionLedgerFromEventFlow : EventFlow → Option AttentionLedgerUp
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
              | filter :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selected :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | omitted :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | publicRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | stream :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | exactness :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | routes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | nameCert ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              some
                                                                                                (AttentionLedgerUp.mk
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    source)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    filter)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    selected)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    omitted)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    publicRow)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    stream)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    transport)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    exactness)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    routes)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    provenance)
                                                                                                  (attentionLedgerDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ ::
                                                                                              _ =>
                                                                                              none

private theorem attentionLedger_round_trip :
    ∀ x : AttentionLedgerUp,
      attentionLedgerFromEventFlow (attentionLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source filter selected omitted publicRow stream transport exactness routes provenance
      nameCert =>
      change
        some
          (AttentionLedgerUp.mk
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist source))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist filter))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist selected))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist omitted))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist publicRow))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist stream))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist transport))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist exactness))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist routes))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist provenance))
            (attentionLedgerDecodeBHist (attentionLedgerEncodeBHist nameCert))) =
          some
            (AttentionLedgerUp.mk source filter selected omitted publicRow stream transport
              exactness routes provenance nameCert)
      rw [attentionLedgerDecode_encode_bhist source,
        attentionLedgerDecode_encode_bhist filter,
        attentionLedgerDecode_encode_bhist selected,
        attentionLedgerDecode_encode_bhist omitted,
        attentionLedgerDecode_encode_bhist publicRow,
        attentionLedgerDecode_encode_bhist stream,
        attentionLedgerDecode_encode_bhist transport,
        attentionLedgerDecode_encode_bhist exactness,
        attentionLedgerDecode_encode_bhist routes,
        attentionLedgerDecode_encode_bhist provenance,
        attentionLedgerDecode_encode_bhist nameCert]

private theorem attentionLedgerToEventFlow_injective {x y : AttentionLedgerUp} :
    attentionLedgerToEventFlow x = attentionLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      attentionLedgerFromEventFlow (attentionLedgerToEventFlow x) =
        attentionLedgerFromEventFlow (attentionLedgerToEventFlow y) :=
    congrArg attentionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (attentionLedger_round_trip x).symm
      (Eq.trans hread (attentionLedger_round_trip y)))

instance attentionLedgerBHistCarrier : BHistCarrier AttentionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := attentionLedgerToEventFlow
  fromEventFlow := attentionLedgerFromEventFlow

instance attentionLedgerChapterTasteGate : ChapterTasteGate AttentionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change attentionLedgerFromEventFlow (attentionLedgerToEventFlow x) = some x
    exact attentionLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (attentionLedgerToEventFlow_injective heq)

instance attentionLedgerFieldFaithful : FieldFaithful AttentionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AttentionLedgerUp.mk source filter selected omitted publicRow stream transport exactness
        routes provenance nameCert =>
        [source, filter, selected, omitted, publicRow, stream, transport, exactness, routes,
          provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ filter₁ selected₁ omitted₁ publicRow₁ stream₁ transport₁ exactness₁ routes₁
        provenance₁ nameCert₁ =>
        cases y with
        | mk source₂ filter₂ selected₂ omitted₂ publicRow₂ stream₂ transport₂ exactness₂
            routes₂ provenance₂ nameCert₂ =>
            cases h
            rfl

def taste_gate : ChapterTasteGate AttentionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  attentionLedgerChapterTasteGate

theorem AttentionLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, attentionLedgerDecodeBHist (attentionLedgerEncodeBHist h) = h) ∧
      (∀ x : AttentionLedgerUp,
        attentionLedgerFromEventFlow (attentionLedgerToEventFlow x) = some x) ∧
        (∀ x y : AttentionLedgerUp,
          attentionLedgerToEventFlow x = attentionLedgerToEventFlow y → x = y) ∧
          attentionLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact attentionLedgerDecode_encode_bhist
  · constructor
    · exact attentionLedger_round_trip
    · constructor
      · intro x y heq
        exact attentionLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.AttentionLedgerUp
