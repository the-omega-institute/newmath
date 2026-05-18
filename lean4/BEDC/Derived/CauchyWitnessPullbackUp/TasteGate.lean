import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWitnessPullbackUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWitnessPullbackUp : Type where
  | mk :
      (gluedSeal classifier realSeal ledger tail synchronizer stream regular dyadic
        agreement transport continuation provenance localName : BHist) →
        CauchyWitnessPullbackUp
  deriving DecidableEq

def cauchyWitnessPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWitnessPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWitnessPullbackEncodeBHist h

def cauchyWitnessPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWitnessPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWitnessPullbackDecodeBHist tail)

private theorem CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyWitnessPullbackDecodeBHist (cauchyWitnessPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyWitnessPullbackToEventFlow :
    CauchyWitnessPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWitnessPullbackUp.mk gluedSeal classifier realSeal ledger tail synchronizer
      stream regular dyadic agreement transport continuation provenance localName =>
      [[BMark.b0],
        cauchyWitnessPullbackEncodeBHist gluedSeal,
        [BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist synchronizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyWitnessPullbackEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist agreement,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessPullbackEncodeBHist localName]

def cauchyWitnessPullbackFromEventFlow :
    EventFlow → Option CauchyWitnessPullbackUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gluedSeal :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | classifier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | tail :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | synchronizer :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | stream :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | regular :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | dyadic ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | agreement ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20
                                                                                        with
                                                                                      | [] =>
                                                                                          none
                                                                                      | transport ::
                                                                                          rest21 =>
                                                                                          match rest21
                                                                                            with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22
                                                                                                with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | continuation ::
                                                                                                  rest23 =>
                                                                                                  match rest23
                                                                                                    with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match rest24
                                                                                                        with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | provenance ::
                                                                                                          rest25 =>
                                                                                                          match rest25
                                                                                                            with
                                                                                                          | [] =>
                                                                                                              none
                                                                                                          | _tag13 ::
                                                                                                              rest26 =>
                                                                                                              match rest26
                                                                                                                with
                                                                                                              | [] =>
                                                                                                                  none
                                                                                                              | localName ::
                                                                                                                  rest27 =>
                                                                                                                  match rest27
                                                                                                                    with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (CauchyWitnessPullbackUp.mk
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            gluedSeal)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            classifier)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            realSeal)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            ledger)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            tail)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            synchronizer)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            stream)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            regular)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            dyadic)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            agreement)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            transport)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            continuation)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            provenance)
                                                                                                                          (cauchyWitnessPullbackDecodeBHist
                                                                                                                            localName))
                                                                                                                  | _ :: _ =>
                                                                                                                      none

private theorem CauchyWitnessPullbackTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyWitnessPullbackUp,
      cauchyWitnessPullbackFromEventFlow (cauchyWitnessPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gluedSeal classifier realSeal ledger tail synchronizer stream regular dyadic
      agreement transport continuation provenance localName =>
      change
        some
          (CauchyWitnessPullbackUp.mk
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist gluedSeal))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist classifier))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist realSeal))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist ledger))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist tail))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist synchronizer))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist stream))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist regular))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist dyadic))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist agreement))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist transport))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist continuation))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist provenance))
            (cauchyWitnessPullbackDecodeBHist
              (cauchyWitnessPullbackEncodeBHist localName))) =
          some
            (CauchyWitnessPullbackUp.mk gluedSeal classifier realSeal ledger tail synchronizer
              stream regular dyadic agreement transport continuation provenance localName)
      rw [CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode gluedSeal,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode classifier,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode realSeal,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode ledger,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode tail,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode synchronizer,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode stream,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode regular,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode dyadic,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode agreement,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode transport,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode continuation,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode provenance,
        CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode localName]

private theorem CauchyWitnessPullbackTasteGate_single_carrier_alignment_injective
    {x y : CauchyWitnessPullbackUp} :
    cauchyWitnessPullbackToEventFlow x = cauchyWitnessPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyWitnessPullbackFromEventFlow (cauchyWitnessPullbackToEventFlow x) =
        cauchyWitnessPullbackFromEventFlow (cauchyWitnessPullbackToEventFlow y) :=
    congrArg cauchyWitnessPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyWitnessPullbackTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyWitnessPullbackTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyWitnessPullbackBHistCarrier :
    BHistCarrier CauchyWitnessPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyWitnessPullbackToEventFlow
  fromEventFlow := cauchyWitnessPullbackFromEventFlow

instance cauchyWitnessPullbackChapterTasteGate :
    ChapterTasteGate CauchyWitnessPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyWitnessPullbackFromEventFlow (cauchyWitnessPullbackToEventFlow x) = some x
    exact CauchyWitnessPullbackTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyWitnessPullbackTasteGate_single_carrier_alignment_injective heq)

instance cauchyWitnessPullbackFieldFaithful :
    FieldFaithful CauchyWitnessPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyWitnessPullbackUp.mk gluedSeal classifier realSeal ledger tail synchronizer
        stream regular dyadic agreement transport continuation provenance localName =>
        [gluedSeal, classifier, realSeal, ledger, tail, synchronizer, stream, regular,
          dyadic, agreement, transport, continuation, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk gluedSeal1 classifier1 realSeal1 ledger1 tail1 synchronizer1 stream1 regular1
        dyadic1 agreement1 transport1 continuation1 provenance1 localName1 =>
        cases y with
        | mk gluedSeal2 classifier2 realSeal2 ledger2 tail2 synchronizer2 stream2 regular2
            dyadic2 agreement2 transport2 continuation2 provenance2 localName2 =>
            cases h
            rfl

instance cauchyWitnessPullbackNontrivial :
    Nontrivial CauchyWitnessPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyWitnessPullbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyWitnessPullbackUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyWitnessPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyWitnessPullbackChapterTasteGate

theorem CauchyWitnessPullbackTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyWitnessPullbackDecodeBHist
      (cauchyWitnessPullbackEncodeBHist h) = h) ∧
      (∀ x : CauchyWitnessPullbackUp, cauchyWitnessPullbackFromEventFlow
        (cauchyWitnessPullbackToEventFlow x) = some x) ∧
        (∀ x y : CauchyWitnessPullbackUp,
          cauchyWitnessPullbackToEventFlow x = cauchyWitnessPullbackToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate CauchyWitnessPullbackUp) ∧
            Nonempty (FieldFaithful CauchyWitnessPullbackUp) ∧
              Nonempty (Nontrivial CauchyWitnessPullbackUp) ∧
                cauchyWitnessPullbackEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyWitnessPullbackTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyWitnessPullbackTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyWitnessPullbackTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨cauchyWitnessPullbackChapterTasteGate⟩,
            ⟨cauchyWitnessPullbackFieldFaithful⟩,
            ⟨cauchyWitnessPullbackNontrivial⟩,
            rfl⟩

end BEDC.Derived.CauchyWitnessPullbackUp.TasteGate

namespace BEDC.Derived.CauchyWitnessPullbackUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CauchyWitnessPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CauchyWitnessPullbackUp
