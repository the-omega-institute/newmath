import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistArity13SequenceNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistArity13SequenceNameCertUp : Type where
  | mk :
      (head first second third fourth fifth sixth seventh eighth ninth tenth eleventh
        tail : BHist) →
      BHistArity13SequenceNameCertUp
  deriving DecidableEq

def bHistArity13SequenceNameCertEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistArity13SequenceNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistArity13SequenceNameCertEncodeBHist h

def bHistArity13SequenceNameCertDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistArity13SequenceNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistArity13SequenceNameCertDecodeBHist tail)

private theorem bHistArity13SequenceNameCertDecode_encode_bhist :
    ∀ h : BHist,
      bHistArity13SequenceNameCertDecodeBHist
        (bHistArity13SequenceNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bHistArity13SequenceNameCertToEventFlow :
    BHistArity13SequenceNameCertUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistArity13SequenceNameCertUp.mk head first second third fourth fifth sixth seventh
      eighth ninth tenth eleventh tail =>
      [[BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist head,
        [BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist first,
        [BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist second,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist third,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist fourth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist fifth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist sixth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist seventh,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist eighth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist ninth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist tenth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist eleventh,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bHistArity13SequenceNameCertEncodeBHist tail]

def bHistArity13SequenceNameCertFromEventFlow :
    EventFlow → Option BHistArity13SequenceNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | head :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | first :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | second :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | third :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | fourth :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | fifth :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sixth :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | seventh :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | eighth :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | ninth :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | tenth :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | eleventh :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | tail :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (BHistArity13SequenceNameCertUp.mk
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist head)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist first)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist second)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist third)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist fourth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist fifth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist sixth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist seventh)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist eighth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist ninth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist tenth)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist eleventh)
                                                                                                                  (bHistArity13SequenceNameCertDecodeBHist tail))
                                                                                                          | _ :: _ => none

private theorem bHistArity13SequenceNameCert_round_trip :
    ∀ x : BHistArity13SequenceNameCertUp,
      bHistArity13SequenceNameCertFromEventFlow
        (bHistArity13SequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk head first second third fourth fifth sixth seventh eighth ninth tenth eleventh tail =>
      change
        some
          (BHistArity13SequenceNameCertUp.mk
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist head))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist first))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist second))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist third))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist fourth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist fifth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist sixth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist seventh))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist eighth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist ninth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist tenth))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist eleventh))
            (bHistArity13SequenceNameCertDecodeBHist
              (bHistArity13SequenceNameCertEncodeBHist tail))) =
          some
            (BHistArity13SequenceNameCertUp.mk head first second third fourth fifth
              sixth seventh eighth ninth tenth eleventh tail)
      rw [bHistArity13SequenceNameCertDecode_encode_bhist head,
        bHistArity13SequenceNameCertDecode_encode_bhist first,
        bHistArity13SequenceNameCertDecode_encode_bhist second,
        bHistArity13SequenceNameCertDecode_encode_bhist third,
        bHistArity13SequenceNameCertDecode_encode_bhist fourth,
        bHistArity13SequenceNameCertDecode_encode_bhist fifth,
        bHistArity13SequenceNameCertDecode_encode_bhist sixth,
        bHistArity13SequenceNameCertDecode_encode_bhist seventh,
        bHistArity13SequenceNameCertDecode_encode_bhist eighth,
        bHistArity13SequenceNameCertDecode_encode_bhist ninth,
        bHistArity13SequenceNameCertDecode_encode_bhist tenth,
        bHistArity13SequenceNameCertDecode_encode_bhist eleventh,
        bHistArity13SequenceNameCertDecode_encode_bhist tail]

private theorem bHistArity13SequenceNameCertToEventFlow_injective
    {x y : BHistArity13SequenceNameCertUp} :
    bHistArity13SequenceNameCertToEventFlow x =
      bHistArity13SequenceNameCertToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bHistArity13SequenceNameCertFromEventFlow
          (bHistArity13SequenceNameCertToEventFlow x) =
        bHistArity13SequenceNameCertFromEventFlow
          (bHistArity13SequenceNameCertToEventFlow y) :=
    congrArg bHistArity13SequenceNameCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bHistArity13SequenceNameCert_round_trip x).symm
      (Eq.trans hread (bHistArity13SequenceNameCert_round_trip y)))

instance bHistArity13SequenceNameCertBHistCarrier :
    BHistCarrier BHistArity13SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistArity13SequenceNameCertToEventFlow
  fromEventFlow := bHistArity13SequenceNameCertFromEventFlow

instance bHistArity13SequenceNameCertChapterTasteGate :
    ChapterTasteGate BHistArity13SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bHistArity13SequenceNameCertFromEventFlow
        (bHistArity13SequenceNameCertToEventFlow x) = some x
    exact bHistArity13SequenceNameCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bHistArity13SequenceNameCertToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BHistArity13SequenceNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bHistArity13SequenceNameCertChapterTasteGate

instance bHistArity13SequenceNameCertFieldFaithful :
    FieldFaithful BHistArity13SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | BHistArity13SequenceNameCertUp.mk head first second third fourth fifth sixth seventh
        eighth ninth tenth eleventh tail =>
        [head, first, second, third, fourth, fifth, sixth, seventh, eighth, ninth,
          tenth, eleventh, tail]
  field_faithful := by
    intro x y h
    cases x with
    | mk head₁ first₁ second₁ third₁ fourth₁ fifth₁ sixth₁ seventh₁ eighth₁ ninth₁
        tenth₁ eleventh₁ tail₁ =>
        cases y with
        | mk head₂ first₂ second₂ third₂ fourth₂ fifth₂ sixth₂ seventh₂ eighth₂ ninth₂
            tenth₂ eleventh₂ tail₂ =>
            injection h with hHead t1
            injection t1 with hFirst t2
            injection t2 with hSecond t3
            injection t3 with hThird t4
            injection t4 with hFourth t5
            injection t5 with hFifth t6
            injection t6 with hSixth t7
            injection t7 with hSeventh t8
            injection t8 with hEighth t9
            injection t9 with hNinth t10
            injection t10 with hTenth t11
            injection t11 with hEleventh t12
            injection t12 with hTail _
            cases hHead
            cases hFirst
            cases hSecond
            cases hThird
            cases hFourth
            cases hFifth
            cases hSixth
            cases hSeventh
            cases hEighth
            cases hNinth
            cases hTenth
            cases hEleventh
            cases hTail
            rfl

instance bHistArity13SequenceNameCertNontrivial :
    Nontrivial BHistArity13SequenceNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BHistArity13SequenceNameCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      BHistArity13SequenceNameCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BHistArity13SequenceNameCert_single_carrier_alignment :
    forall x : BHistArity13SequenceNameCertUp,
      bHistArity13SequenceNameCertFromEventFlow
        (bHistArity13SequenceNameCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact bHistArity13SequenceNameCert_round_trip

end BEDC.Derived.BHistArity13SequenceNameCertUp
