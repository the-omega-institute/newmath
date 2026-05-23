import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FocusedMultiHistLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FocusedMultiHistLedgerUp : Type where
  | mk :
      (focusedState localFrame kernelTrace traceSeal gapLedger relationLedger invariantReadback
        dependenceRoute auditRow transportRow replayRoute provenance nameCert : BHist) →
      FocusedMultiHistLedgerUp

def focusedMultiHistLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: focusedMultiHistLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: focusedMultiHistLedgerEncodeBHist h

def focusedMultiHistLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (focusedMultiHistLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (focusedMultiHistLedgerDecodeBHist tail)

private theorem focusedMultiHistLedgerDecode_encode_bhist :
    ∀ h : BHist, focusedMultiHistLedgerDecodeBHist
      (focusedMultiHistLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def focusedMultiHistLedgerToEventFlow : FocusedMultiHistLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FocusedMultiHistLedgerUp.mk focusedState localFrame kernelTrace traceSeal gapLedger
      relationLedger invariantReadback dependenceRoute auditRow transportRow replayRoute
      provenance nameCert =>
      [[BMark.b0],
        focusedMultiHistLedgerEncodeBHist focusedState,
        [BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist localFrame,
        [BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist kernelTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist traceSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist gapLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist relationLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist invariantReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        focusedMultiHistLedgerEncodeBHist dependenceRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist auditRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist replayRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        focusedMultiHistLedgerEncodeBHist nameCert]

def focusedMultiHistLedgerFromEventFlow : EventFlow → Option FocusedMultiHistLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | focusedState :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | localFrame :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | kernelTrace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | traceSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gapLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | relationLedger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | invariantReadback :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | dependenceRoute ::
                                                                  rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | auditRow ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | transportRow ::
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
                                                                                      | replayRoute ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | provenance ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | nameCert ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (FocusedMultiHistLedgerUp.mk
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    focusedState)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    localFrame)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    kernelTrace)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    traceSeal)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    gapLedger)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    relationLedger)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    invariantReadback)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    dependenceRoute)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    auditRow)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    transportRow)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    replayRoute)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (focusedMultiHistLedgerDecodeBHist
                                                                                                                    nameCert))
                                                                                                          | _ ::
                                                                                                              _ =>
                                                                                                              none

private theorem focusedMultiHistLedger_round_trip :
    ∀ x : FocusedMultiHistLedgerUp,
      focusedMultiHistLedgerFromEventFlow (focusedMultiHistLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk focusedState localFrame kernelTrace traceSeal gapLedger relationLedger invariantReadback
      dependenceRoute auditRow transportRow replayRoute provenance nameCert =>
      change
        some
          (FocusedMultiHistLedgerUp.mk
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist focusedState))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist localFrame))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist kernelTrace))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist traceSeal))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist gapLedger))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist relationLedger))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist invariantReadback))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist dependenceRoute))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist auditRow))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist transportRow))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist replayRoute))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist provenance))
            (focusedMultiHistLedgerDecodeBHist
              (focusedMultiHistLedgerEncodeBHist nameCert))) =
          some
            (FocusedMultiHistLedgerUp.mk focusedState localFrame kernelTrace traceSeal
              gapLedger relationLedger invariantReadback dependenceRoute auditRow transportRow
              replayRoute provenance nameCert)
      rw [focusedMultiHistLedgerDecode_encode_bhist focusedState,
        focusedMultiHistLedgerDecode_encode_bhist localFrame,
        focusedMultiHistLedgerDecode_encode_bhist kernelTrace,
        focusedMultiHistLedgerDecode_encode_bhist traceSeal,
        focusedMultiHistLedgerDecode_encode_bhist gapLedger,
        focusedMultiHistLedgerDecode_encode_bhist relationLedger,
        focusedMultiHistLedgerDecode_encode_bhist invariantReadback,
        focusedMultiHistLedgerDecode_encode_bhist dependenceRoute,
        focusedMultiHistLedgerDecode_encode_bhist auditRow,
        focusedMultiHistLedgerDecode_encode_bhist transportRow,
        focusedMultiHistLedgerDecode_encode_bhist replayRoute,
        focusedMultiHistLedgerDecode_encode_bhist provenance,
        focusedMultiHistLedgerDecode_encode_bhist nameCert]

private theorem focusedMultiHistLedgerToEventFlow_injective {x y : FocusedMultiHistLedgerUp} :
    focusedMultiHistLedgerToEventFlow x = focusedMultiHistLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      focusedMultiHistLedgerFromEventFlow (focusedMultiHistLedgerToEventFlow x) =
        focusedMultiHistLedgerFromEventFlow (focusedMultiHistLedgerToEventFlow y) :=
    congrArg focusedMultiHistLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (focusedMultiHistLedger_round_trip x).symm
      (Eq.trans hread (focusedMultiHistLedger_round_trip y)))

instance focusedMultiHistLedgerBHistCarrier : BHistCarrier FocusedMultiHistLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := focusedMultiHistLedgerToEventFlow
  fromEventFlow := focusedMultiHistLedgerFromEventFlow

instance focusedMultiHistLedgerChapterTasteGate :
    ChapterTasteGate FocusedMultiHistLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change focusedMultiHistLedgerFromEventFlow
      (focusedMultiHistLedgerToEventFlow x) = some x
    exact focusedMultiHistLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (focusedMultiHistLedgerToEventFlow_injective heq)

instance focusedMultiHistLedgerFieldFaithful :
    FieldFaithful FocusedMultiHistLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FocusedMultiHistLedgerUp.mk focusedState localFrame kernelTrace traceSeal gapLedger
        relationLedger invariantReadback dependenceRoute auditRow transportRow replayRoute
        provenance nameCert =>
        [focusedState, localFrame, kernelTrace, traceSeal, gapLedger, relationLedger,
          invariantReadback, dependenceRoute, auditRow, transportRow, replayRoute, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk focusedState₁ localFrame₁ kernelTrace₁ traceSeal₁ gapLedger₁ relationLedger₁
        invariantReadback₁ dependenceRoute₁ auditRow₁ transportRow₁ replayRoute₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk focusedState₂ localFrame₂ kernelTrace₂ traceSeal₂ gapLedger₂ relationLedger₂
            invariantReadback₂ dependenceRoute₂ auditRow₂ transportRow₂ replayRoute₂ provenance₂
            nameCert₂ =>
            cases h
            rfl

def taste_gate : ChapterTasteGate FocusedMultiHistLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  focusedMultiHistLedgerChapterTasteGate

theorem FocusedMultiHistLedgerUp_single_carrier_alignment :
    (∀ h : BHist, focusedMultiHistLedgerDecodeBHist
      (focusedMultiHistLedgerEncodeBHist h) = h) ∧
      (∀ x : FocusedMultiHistLedgerUp,
        focusedMultiHistLedgerFromEventFlow
          (focusedMultiHistLedgerToEventFlow x) = some x) ∧
        (∀ x y : FocusedMultiHistLedgerUp,
          focusedMultiHistLedgerToEventFlow x =
            focusedMultiHistLedgerToEventFlow y → x = y) ∧
          focusedMultiHistLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact focusedMultiHistLedgerDecode_encode_bhist
  · constructor
    · exact focusedMultiHistLedger_round_trip
    · constructor
      · intro x y heq
        exact focusedMultiHistLedgerToEventFlow_injective heq
      · rfl

theorem FocusedMultiHistLedgerCarrier_nonescape
    {S F K T G R I D O H C P N S' F' K' T' G' R' I' D' O' H' C' P' N' : BHist}
    (heq :
      focusedMultiHistLedgerToEventFlow
          (FocusedMultiHistLedgerUp.mk S F K T G R I D O H C P N) =
        focusedMultiHistLedgerToEventFlow
          (FocusedMultiHistLedgerUp.mk S' F' K' T' G' R' I' D' O' H' C' P' N'))
    (htrace : Cont S F K) (hledger : Cont G R I) :
    hsame S S' ∧ hsame F F' ∧ hsame K K' ∧ hsame T T' ∧ hsame G G' ∧
      hsame R R' ∧ hsame I I' ∧ hsame N N' ∧ Cont S' F' K' ∧ Cont G' R' I' := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  have hmk :=
    focusedMultiHistLedgerToEventFlow_injective
      (x := FocusedMultiHistLedgerUp.mk S F K T G R I D O H C P N)
      (y := FocusedMultiHistLedgerUp.mk S' F' K' T' G' R' I' D' O' H' C' P' N')
      heq
  cases hmk
  exact
    ⟨hsame_refl S, hsame_refl F, hsame_refl K, hsame_refl T, hsame_refl G,
      hsame_refl R, hsame_refl I, hsame_refl N, htrace, hledger⟩

end BEDC.Derived.FocusedMultiHistLedgerUp
