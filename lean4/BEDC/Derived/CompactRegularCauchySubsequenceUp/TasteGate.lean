import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRegularCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRegularCauchySubsequenceUp : Type where
  | mk :
      (compactSource sourceWindow reindexLedger selectedWindow dyadicLedger regularReadback
        realSeal transport replay provenance name : BHist) →
      CompactRegularCauchySubsequenceUp
  deriving DecidableEq

def compactRegularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRegularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRegularCauchySubsequenceEncodeBHist h

def compactRegularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRegularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRegularCauchySubsequenceDecodeBHist tail)

private theorem compactRegularCauchySubsequence_decode_encode_bhist :
    ∀ h : BHist,
      compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactRegularCauchySubsequenceToEventFlow :
    CompactRegularCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRegularCauchySubsequenceUp.mk compactSource sourceWindow reindexLedger
      selectedWindow dyadicLedger regularReadback realSeal transport replay provenance name =>
      [[BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist compactSource,
        [BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist sourceWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist reindexLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist selectedWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactRegularCauchySubsequenceEncodeBHist name]

def compactRegularCauchySubsequenceFromEventFlow :
    EventFlow → Option CompactRegularCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | compactSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | reindexLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | selectedWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadicLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | regularReadback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | realSeal :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | replay ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              none
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
                                                                                      | name ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CompactRegularCauchySubsequenceUp.mk
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist compactSource)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist sourceWindow)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist reindexLedger)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist selectedWindow)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist dyadicLedger)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist regularReadback)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist realSeal)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist transport)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist replay)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist provenance)
                                                                                                  (compactRegularCauchySubsequenceDecodeBHist name))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem compactRegularCauchySubsequence_round_trip :
    ∀ x : CompactRegularCauchySubsequenceUp,
      compactRegularCauchySubsequenceFromEventFlow
          (compactRegularCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource sourceWindow reindexLedger selectedWindow dyadicLedger
      regularReadback realSeal transport replay provenance name =>
      change
        some
          (CompactRegularCauchySubsequenceUp.mk
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist compactSource))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist sourceWindow))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist reindexLedger))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist selectedWindow))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist dyadicLedger))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist regularReadback))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist realSeal))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist transport))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist replay))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist provenance))
            (compactRegularCauchySubsequenceDecodeBHist
              (compactRegularCauchySubsequenceEncodeBHist name))) =
          some
            (CompactRegularCauchySubsequenceUp.mk compactSource sourceWindow
              reindexLedger selectedWindow dyadicLedger regularReadback realSeal transport
              replay provenance name)
      rw [compactRegularCauchySubsequence_decode_encode_bhist compactSource,
        compactRegularCauchySubsequence_decode_encode_bhist sourceWindow,
        compactRegularCauchySubsequence_decode_encode_bhist reindexLedger,
        compactRegularCauchySubsequence_decode_encode_bhist selectedWindow,
        compactRegularCauchySubsequence_decode_encode_bhist dyadicLedger,
        compactRegularCauchySubsequence_decode_encode_bhist regularReadback,
        compactRegularCauchySubsequence_decode_encode_bhist realSeal,
        compactRegularCauchySubsequence_decode_encode_bhist transport,
        compactRegularCauchySubsequence_decode_encode_bhist replay,
        compactRegularCauchySubsequence_decode_encode_bhist provenance,
        compactRegularCauchySubsequence_decode_encode_bhist name]

private theorem compactRegularCauchySubsequenceToEventFlow_injective
    {x y : CompactRegularCauchySubsequenceUp} :
    compactRegularCauchySubsequenceToEventFlow x =
        compactRegularCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRegularCauchySubsequenceFromEventFlow
          (compactRegularCauchySubsequenceToEventFlow x) =
        compactRegularCauchySubsequenceFromEventFlow
          (compactRegularCauchySubsequenceToEventFlow y) :=
    congrArg compactRegularCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactRegularCauchySubsequence_round_trip x).symm
      (Eq.trans hread (compactRegularCauchySubsequence_round_trip y)))

instance compactRegularCauchySubsequenceBHistCarrier :
    BHistCarrier CompactRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRegularCauchySubsequenceToEventFlow
  fromEventFlow := compactRegularCauchySubsequenceFromEventFlow

instance compactRegularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate CompactRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRegularCauchySubsequenceFromEventFlow
          (compactRegularCauchySubsequenceToEventFlow x) =
        some x
    exact compactRegularCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactRegularCauchySubsequenceToEventFlow_injective heq)

theorem CompactRegularCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRegularCauchySubsequenceDecodeBHist
          (compactRegularCauchySubsequenceEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CompactRegularCauchySubsequenceUp) ∧
        Nonempty (ChapterTasteGate CompactRegularCauchySubsequenceUp) ∧
          compactRegularCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactRegularCauchySubsequence_decode_encode_bhist
  · constructor
    · exact Nonempty.intro compactRegularCauchySubsequenceBHistCarrier
    · constructor
      · exact Nonempty.intro compactRegularCauchySubsequenceChapterTasteGate
      · rfl

end BEDC.Derived.CompactRegularCauchySubsequenceUp
